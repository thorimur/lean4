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

A *stage* is a fresh directory that a sandboxed build process may write, and nothing else. Lake
copies the expected outputs out of the stage afterwards, hashing them in memory, so that a recorded
hash always describes the bytes the process produced, whatever other processes do to the files
in place.

Build actions (e.g., `compileLeanModule`) declare that their processes run in a stage by using
`withStage?`. Stages exist only when the build is sandboxed (`BuildConfig.sandbox?`).
-/

open System

namespace Lake

/-- A directory that is the only writable location of the sandboxed processes of one build job. -/
public structure Stage where
  /-- The build key of the fetch whose job created the stage. -/
  key : BuildKey
  /-- The canonical path of the stage directory. -/
  dir : FilePath

namespace Stage

/-- The name of the scratch directory in a stage, which sandboxed processes use as `TMPDIR`. -/
public def tmpDirName : String := "tmp"

/-- The directory under which Lake creates stages. -/
def rootDir : JobM FilePath :=
  return (← getRootPackage).buildDir / "stage"

/-- A file name for `key` that is readable and free of path separators. -/
def keyDirName (key : BuildKey) : String :=
  key.toString.map fun c => if c.isAlphanum || c == '.' || c == '-' || c == '_' then c else '_'

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
    error s!"{stage.key}: unexpected entry '{entry.fileName}' in stage '{stage.dir}'"
  for (name, dest) in found do
    stage.install name dest

end Stage

/--
Runs `act` with a fresh stage and the build's sandbox if the build is sandboxed, or with `none`
otherwise. The stage belongs to the innermost fetch and is deleted once `act` finishes.
-/
public def withStage? (act : Option (SandboxConfig × Stage) → JobM α) : JobM α := do
  let some cfg ← getSandbox? | act none
  let key := (← getCallStack).head?.getD default
  let root ← Stage.rootDir
  IO.FS.createDirAll root
  let dir ← Stage.createFreshDir (root / Stage.keyDirName key).toString
  let dir ← IO.FS.realPath dir
  IO.FS.createDir (dir / Stage.tmpDirName)
  try
    act (some (cfg, {key, dir}))
  finally
    IO.FS.removeDirAll dir
