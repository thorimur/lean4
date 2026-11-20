/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

prelude
public import Lake.Build.Job.Monad
import Lake.Build.Common
import Lake.Util.IO

/-! # Build Stages

A *stage* is a fresh directory owned by Lake, holding a directory that a sandboxed build process
may write, and nothing else. Lake copies the expected outputs out of the stage afterwards, hashing
them in memory, so that a recorded hash always describes the bytes the process produced, whatever
other processes do to the files in place.

Lake never deletes a stage's contents itself: a process in the same sandbox does (see
`Stage.cleanup`), so that symbolic links or other tricks of sandboxed code cannot redirect a
deletion outside the stage.

Build actions (e.g., `compileLeanModule`) declare that their processes run in a stage by using
`withStage?`. Stages exist only when the build is sandboxed (`BuildConfig.sandbox?`).
-/

open System

namespace Lake

/-- A directory that is the only writable location of the sandboxed processes of one build job. -/
public structure Stage where
  /-- The build key of the fetch whose job created the stage, or `none` outside of any fetch. -/
  key? : Option BuildKey
  /-- The stage's own directory, which sandboxed processes cannot modify. -/
  root : FilePath
  /-- The directory sandboxed processes may write: `writableDirName` in `root`. -/
  dir : FilePath

namespace Stage

/-- The name of the writable directory in a stage's own directory. -/
public def writableDirName : String := "w"

/-- The name of the scratch directory in a stage, which sandboxed processes use as `TMPDIR`. -/
public def tmpDirName : String := "tmp"

/-- The directory under which Lake creates stages. -/
def rootDir : JobM FilePath :=
  return (← getRootPackage).buildDir / "stage"

/-- The owner of the stage in names and messages: its build key, or `unkeyed`. -/
public def owner (stage : Stage) : String :=
  stage.key?.elim "unkeyed" toString

/--
The base name of the stages of the build key `key?`: a readable prefix of the key, with characters
other than ASCII letters, digits, `.`, `-` and `_` replaced by `_`, and the hash of the full key,
which tells apart keys that look alike in that prefix (also on case-insensitive file systems).
Stages are unique because they are created exclusively, not because of this name.
-/
def baseName (key? : Option BuildKey) : String :=
  let full := key?.elim "unkeyed" toString
  let safe := full.map fun c => if c.isAlphanum || c == '.' || c == '-' || c == '_' then c else '_'
  s!"{(safe.take 64).copy}-{(Hash.ofString full).hex}"

/-- Creates `base-n` for the least `n` for which it does not yet exist, and returns its path. -/
partial def createFreshDir (base : String) (n : Nat := 0) : IO FilePath := do
  let dir : FilePath := s!"{base}-{n}"
  try
    IO.FS.createDir dir
    return dir
  catch
    | .alreadyExists .. => createFreshDir base (n + 1)
    | e => throw e

/-- Runs `args` in the stage under the sandbox `cfg`. -/
public def spawnArgs (stage : Stage) (cfg : SandboxConfig) (args : IO.Process.SpawnArgs) :
    IO.Process.SpawnArgs :=
  let env := args.env.push ("TMPDIR", some (stage.dir / tmpDirName).toString)
  match (cfg.command stage.dir).toList with
  | [] => {args with env}
  | cmd :: pre => {args with cmd, args := pre.toArray.push args.cmd ++ args.args, env}

/--
Copies the regular file `name` out of the stage to `dest`, writing its hash, computed from the
copied bytes, to `dest`'s `.hash` file. `dest` is replaced by a new file, so processes that still
hold the staged file open cannot modify `dest`.
-/
public def install (stage : Stage) (name : String) (dest : FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile (stage.dir / name)
  createParentDirs dest
  let tmp := dest.addExtension "stage.tmp"
  IO.FS.writeBinFile tmp bytes
  IO.FS.rename tmp dest
  writeFileHash dest (Hash.ofByteArray bytes)

/--
Installs the files the stage's process produced. `outputs` maps the names of the expected files to
their destinations. Expected files that are missing are skipped. Any other entry in the stage, apart
from its scratch directory, is an error, and nothing is installed.
-/
public def finish (stage : Stage) (outputs : Array (String × FilePath)) : JobM Unit := do
  let mut found := #[]
  for entry in ← stage.dir.readDir do
    if entry.fileName == tmpDirName then
      continue
    let isFile := (← entry.path.symlinkMetadata).type == .file
    if let some (_, dest) := outputs.find? (·.1 == entry.fileName) then
      if isFile then
        found := found.push (entry.fileName, dest)
        continue
    error s!"{stage.owner}: unexpected entry '{entry.fileName}' in stage '{stage.dir}'"
  for (name, dest) in found do
    stage.install name dest

/--
Deletes the stage. A process in the stage's sandbox deletes the contents of the writable directory
with `find -delete`, which follows no symbolic link, not even to the directory itself, and the
sandbox denies deleting anything outside it. Lake itself then only removes the two directories with
`rmdir`, which removes nothing but an empty directory. If a step fails, the stage is left in place
with a warning; Lake never deletes it recursively outside the sandbox.
-/
def cleanup (stage : Stage) (cfg : SandboxConfig) : JobM Unit := do
  if (cfg.command stage.dir).isEmpty then
    logWarning s!"{stage.owner}: stage '{stage.root}' left in place: no sandbox to delete it in"
    return
  let find := stage.spawnArgs cfg {
    cmd := "find", args := #[stage.dir.toString, "-mindepth", "1", "-delete"] }
  let emptied ← (do return (← IO.Process.output find).exitCode == 0 : IO Bool).catchExceptions
    fun _ => pure false
  if emptied then
    let removed ← (do IO.FS.removeDir stage.dir; IO.FS.removeDir stage.root; return true : IO Bool)
      |>.catchExceptions fun _ => pure false
    if removed then
      return
  logWarning s!"{stage.owner}: stage '{stage.root}' left in place: could not delete it"

end Stage

/--
Runs `act` with a fresh stage and the build's sandbox if the build is sandboxed, or with `none`
otherwise. The stage belongs to the innermost fetch and is deleted once `act` finishes.
-/
public def withStage? (act : Option (SandboxConfig × Stage) → JobM α) : JobM α := do
  let some cfg ← getSandbox? | act none
  let key? := (← getCallStack).head?
  let stages ← Stage.rootDir
  IO.FS.createDirAll stages
  -- Canonicalized before creating the stage, so the stage's path is exactly the directory created
  let stages ← IO.FS.realPath stages
  let root ← Stage.createFreshDir (stages / Stage.baseName key?).toString
  let stage := {key?, root, dir := root / Stage.writableDirName}
  IO.FS.createDir stage.dir
  IO.FS.createDir (stage.dir / Stage.tmpDirName)
  try
    act (some (cfg, stage))
  finally
    stage.cleanup cfg
