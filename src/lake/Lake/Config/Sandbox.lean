/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

prelude
public import Init.System.FilePath
import Init.Data.String.Search

open System (FilePath)

namespace Lake

/--
How Lake confines the processes of build actions that declare a stage (e.g., `lean` and `leanir`).

Such a process may write only to its stage directory. Lake then copies the expected outputs out of
the stage, hashing them in memory, and rejects any other file left in it.
-/
public structure SandboxConfig where
  /--
  The command prefix that runs the rest of the command line in a sandbox whose only writable
  location is the given stage directory (a canonical path).
  -/
  command : FilePath → Array String

public instance : Inhabited SandboxConfig := ⟨{command := fun _ => #[]}⟩

namespace SandboxConfig

/--
A `bwrap` sandbox: the file system is read-only except for the stage, and every process the
sandboxed command starts is killed when it exits.
-/
public def bwrap : SandboxConfig where
  command stage := #[
    "bwrap", "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
    "--bind", stage.toString, stage.toString,
    "--unshare-pid", "--die-with-parent", "--"]

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
  command stage := #["sandbox-exec", "-D", "STAGE=" ++ stage.toString, "-p", seatbeltProfile]

/--
A Linux Landlock sandbox run by `runner` (`lake-sandbox-run`): writes are denied outside the stage
and `/dev/null`. Processes the sandboxed command starts may outlive it, but they remain confined.
-/
public def landlock (runner : FilePath) : SandboxConfig where
  command stage := #[runner.toString, stage.toString, "--"]

/--
Like `SandboxConfig.landlock`, but the runner also kills every process the sandboxed command
started once the command exits, so none outlives it.
-/
public def landlockReap (runner : FilePath) : SandboxConfig where
  command stage := #[runner.toString, "--reap", stage.toString, "--"]

/--
A sandbox given by a command template, as in a JSON configuration file: each occurrence of
`{stage}` in an element is replaced with the stage directory.
-/
public def ofTemplate (template : Array String) : SandboxConfig where
  command stage := template.map (·.replace "{stage}" stage.toString)

end SandboxConfig
