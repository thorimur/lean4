/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

prelude
public import Init.System.IO
import Init.Data.String.Search

open System (FilePath)
open IO.Process (SpawnArgs)

namespace Lake

/--
How Lake confines the processes of build actions that declare a stage (e.g., `lean` and `leanir`).

Such a process may write only to its stage directory. Lake then copies the expected outputs out of
the stage, hashing them in memory, and rejects any other file left in it.
-/
public structure SandboxConfig where
  /--
  Turns a command into one that runs it in a sandbox whose only writable location is the stage
  directory `stage` (a canonical path). Configurations that leave the command unchanged are
  treated as unsandboxed.

  The other fields of the `SpawnArgs` (environment, working directory, standard streams) then
  apply to the sandbox's own process, which must pass them on to the sandboxed command, as all the
  presets do, or translate them into its own options.
  -/
  wrap : (stage : FilePath) → SpawnArgs → SpawnArgs

public instance : Inhabited SandboxConfig := ⟨{wrap := fun _ args => args}⟩

namespace SandboxConfig

/--
A `bwrap` sandbox: the file system is read-only except for the stage, and every process the
sandboxed command starts is killed when it exits.
-/
public def bwrap : SandboxConfig where
  wrap stage args := {args with
    cmd := "bwrap"
    args := #[
      "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
      "--bind", stage.toString, stage.toString,
      "--unshare-pid", "--die-with-parent", "--", args.cmd] ++ args.args
  }

/-- The Seatbelt profile of `SandboxConfig.seatbelt`, parameterized by `STAGE`. -/
def seatbeltProfile : String :=
  "(version 1)(allow default)(deny file-write*)\
  (allow file-write* (subpath (param \"STAGE\")) \
  (literal \"/dev/null\") (literal \"/dev/dtracehelper\") (regex #\"^/dev/tty\"))"

/--
A macOS Seatbelt (`sandbox-exec`) sandbox: writes are denied outside the stage and a few devices.
Unlike `bwrap`, processes the sandboxed command starts may outlive it, but they remain confined.
-/
public def seatbelt : SandboxConfig where
  wrap stage args := {args with
    cmd := "sandbox-exec"
    args := #["-D", "STAGE=" ++ stage.toString, "-p", seatbeltProfile, args.cmd] ++ args.args
  }

/--
A Linux Landlock sandbox run by `runner` (`lake-sandbox-run`): writes are denied outside the stage
and `/dev/null`. Processes the sandboxed command starts may outlive it, but they remain confined.
-/
public def landlock (runner : FilePath) : SandboxConfig where
  wrap stage args := {args with
    cmd := runner.toString
    args := #[stage.toString, "--", args.cmd] ++ args.args
  }

/--
Like `SandboxConfig.landlock`, but the runner also kills every process the sandboxed command
started once the command exits, so none outlives it.
-/
public def landlockReap (runner : FilePath) : SandboxConfig where
  wrap stage args := {args with
    cmd := runner.toString
    args := #["--reap", stage.toString, "--", args.cmd] ++ args.args
  }

/-- The Landlock rights that change the file system, as `setpriv` names them. -/
def setprivWriteRights : String :=
  "write-file,remove-dir,remove-file,make-char,make-dir,make-reg,make-sock,make-fifo,make-block,\
  make-sym,refer,truncate"

/--
Like `SandboxConfig.landlock`, but run by util-linux's `setpriv` (with its Landlock options) instead
of Lake's own runner.
-/
public def landlockSetpriv : SandboxConfig where
  wrap stage args := {args with
    cmd := "setpriv"
    args := #[
      "--nnp", "--landlock-access", "fs:" ++ setprivWriteRights,
      "--landlock-rule", "path-beneath:" ++ setprivWriteRights ++ ":" ++ stage.toString,
      "--landlock-rule", "path-beneath:write-file,truncate:/dev/null",
      "--", args.cmd] ++ args.args
  }

/--
A sandbox given by a command template, as in a JSON configuration file. The template is the
sandbox's command line: in each element, `{stage}` is replaced by the stage directory, and the
element `{command}` is replaced by the sandboxed command and its arguments. The template must
contain `{command}` exactly once, and not as its first element, which names the sandbox's program.
The sandbox's program must pass its environment and working directory on to the sandboxed command.
-/
public def ofTemplate (template : Array String) : Except String SandboxConfig := do
  let some program := template[0]?
    | throw "`command` must not be empty"
  let some pos := template.idxOf? "{command}"
    | throw "`command` must contain the element `{command}`, where the sandboxed command goes"
  if pos == 0 then
    throw "`command` must start with the sandbox's program, not `{command}`"
  if template.count "{command}" > 1 then
    throw "`command` must contain `{command}` only once"
  let before := template.extract 1 pos
  let after := template.extract (pos + 1) template.size
  return {
    wrap stage args :=
      let fill (elem : String) := elem.replace "{stage}" stage.toString
      {args with
        cmd := fill program
        args := before.map fill ++ #[args.cmd] ++ args.args ++ after.map fill
      }
  }

end SandboxConfig
