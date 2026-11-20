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

  The environment (`env`, `inheritEnv`) and working directory (`cwd`) of the given `SpawnArgs`
  apply inside the sandbox, to the command alone; the sandbox's own program runs with Lake's.
  Its standard streams and `setsid` apply to the sandbox's program, whose process tree the
  command joins.
  -/
  wrap : (stage : FilePath) → SpawnArgs → SpawnArgs

public instance : Inhabited SandboxConfig := ⟨{wrap := fun _ args => args}⟩

namespace SandboxConfig

/--
The `SpawnArgs` of a sandbox's program `cmd` with arguments `argv`, which runs the command
`args` describes: Lake's environment and working directory, and the standard streams and session
of `args`.
-/
def sandboxProgram (args : SpawnArgs) (cmd : String) (argv : Array String) : SpawnArgs where
  cmd
  args := argv
  stdin := args.stdin
  stdout := args.stdout
  stderr := args.stderr
  setsid := args.setsid

/-- The final change to each environment variable in `env`, where later entries win. -/
def envChanges (env : Array (String × Option String)) : Array (String × Option String) :=
  env.foldl (init := #[]) fun acc (var, val?) => (acc.filter (·.1 != var)).push (var, val?)

/--
An `env` command line that runs the command `args` describes with its environment and working
directory. A command whose name contains `=` cannot be run this way, since `env` would take it
for a variable assignment.
-/
def envCommandLine (args : SpawnArgs) : Array String := Id.run do
  let changes := envChanges args.env
  let mut argv := #["env"]
  unless args.inheritEnv do
    argv := argv.push "-i"
  for (var, val?) in changes do
    if val?.isNone then
      argv := argv ++ #["-u", var]
  if let some cwd := args.cwd then
    argv := argv ++ #["-C", cwd.toString]
  argv := argv.push "--"
  for (var, val?) in changes do
    if let some val := val? then
      argv := argv.push (var ++ "=" ++ val)
  return argv.push args.cmd ++ args.args

/--
A `bwrap` sandbox: the file system is read-only except for the stage, and every process the
sandboxed command starts is killed when it exits.
-/
public def bwrap : SandboxConfig where
  wrap stage args := Id.run do
    let mut argv := #[
      "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
      "--bind", stage.toString, stage.toString,
      "--unshare-pid", "--die-with-parent"]
    unless args.inheritEnv do
      argv := argv.push "--clearenv"
    for (var, val?) in envChanges args.env do
      match val? with
      | some val => argv := argv ++ #["--setenv", var, val]
      | none => argv := argv ++ #["--unsetenv", var]
    if let some cwd := args.cwd then
      argv := argv ++ #["--chdir", cwd.toString]
    return sandboxProgram args "bwrap" (argv ++ #["--", args.cmd] ++ args.args)

/-- The Seatbelt profile of `SandboxConfig.seatbelt`, parameterized by `STAGE`. -/
def seatbeltProfile : String :=
  "(version 1)(allow default)(deny file-write*)\
  (allow file-write* (subpath (param \"STAGE\")) \
  (literal \"/dev/null\") (literal \"/dev/dtracehelper\") (regex #\"^/dev/tty\"))"

/--
A macOS Seatbelt (`sandbox-exec`) sandbox: writes are denied outside the stage and a few devices.
Unlike `bwrap`, processes the sandboxed command starts may outlive it, but they remain confined.
As `sandbox-exec` is protected by System Integrity Protection, `DYLD_*` variables do not reach the
sandboxed command.
-/
public def seatbelt : SandboxConfig where
  wrap stage args := sandboxProgram args "sandbox-exec" <|
    #["-D", "STAGE=" ++ stage.toString, "-p", seatbeltProfile] ++ envCommandLine args

/--
A Linux Landlock sandbox run by `runner` (`lake-sandbox-run`): writes are denied outside the stage
and `/dev/null`. Processes the sandboxed command starts may outlive it, but they remain confined.
-/
public def landlock (runner : FilePath) : SandboxConfig where
  wrap stage args := sandboxProgram args runner.toString <|
    #[stage.toString, "--"] ++ envCommandLine args

/--
Like `SandboxConfig.landlock`, but the runner also kills every process the sandboxed command
started once the command exits, so none outlives it.
-/
public def landlockReap (runner : FilePath) : SandboxConfig where
  wrap stage args := sandboxProgram args runner.toString <|
    #["--reap", stage.toString, "--"] ++ envCommandLine args

/-- The Landlock rights that change the file system, as `setpriv` names them. -/
def setprivWriteRights : String :=
  "write-file,remove-dir,remove-file,make-char,make-dir,make-reg,make-sock,make-fifo,make-block,\
  make-sym,refer,truncate"

/--
Like `SandboxConfig.landlock`, but run by util-linux's `setpriv` (with its Landlock options) instead
of Lake's own runner.
-/
public def landlockSetpriv : SandboxConfig where
  wrap stage args := sandboxProgram args "setpriv" <|
    #["--nnp", "--landlock-access", "fs:" ++ setprivWriteRights,
      "--landlock-rule", "path-beneath:" ++ setprivWriteRights ++ ":" ++ stage.toString,
      "--landlock-rule", "path-beneath:write-file,truncate:/dev/null", "--"] ++ envCommandLine args

/--
A sandbox given by a command template, as in a JSON configuration file. The template is the
sandbox's command line: in each element, `{stage}` is replaced by the stage directory, and the
element `{command}` is replaced by an `env` command line that runs the sandboxed command with its
environment and working directory. The template must contain `{command}` exactly once, and not as
its first element, which names the sandbox's program.
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
      sandboxProgram args (fill program) <|
        before.map fill ++ envCommandLine args ++ after.map fill
  }

end SandboxConfig
