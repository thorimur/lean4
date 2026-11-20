/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat, Thomas R. Murrills
-/
module

prelude
public import Lake.Build.Stage
import Lake.Util.Proc
import Lake.Util.FilePath
import Lake.Util.IO
import Init.Data.String.Search
import Lean.CoreM
import Lean.Compiler.Options

/-! # Lean Build Actions

Actions that run the Lean toolchain on a module. They run in a stage (see `withStage?`), so when the
build is sandboxed, `lean` and `leanir` can write only their own outputs.
-/

open System
open Lean hiding SearchPath

namespace Lake
-- for dot notation on the `Lake.Lean.ModuleArtifacts` helpers below
open Lake

/-- The names of the outputs to copy out of a stage, paired with their destinations. -/
def stageOutputs (outputs : Array FilePath) : Array (String × FilePath) :=
  outputs.filterMap fun p => p.fileName.map (·, p)

def runLeanIR
  (setupFile irFile cFile : FilePath) (leanPath : SearchPath) (leanir : FilePath)
  (wrap : IO.Process.SpawnArgs → IO.Process.SpawnArgs)
: LogIO Unit := do
  createParentDirs irFile
  createParentDirs cFile
  proc <| wrap {
    cmd := leanir.toString
    args := #[setupFile.toString, irFile.toString, cFile.toString]
    env := #[("LEAN_PATH", leanPath.toString)]
  }

public def compileLeanIR
  (setupFile irFile cFile : FilePath)
  (leanPath : SearchPath := [])
  (leanir : FilePath := "leanir")
: JobM Unit := withStage? fun
  | none => runLeanIR setupFile irFile cFile leanPath leanir id
  | some (cfg, stage) => do
    -- `leanir` writes the `.ir.sig` next to the `.ir`
    let outputs := stageOutputs #[irFile, irFile.addExtension "sig", cFile]
    let inStage (p : FilePath) := stage.dir / (p.fileName.getD "")
    runLeanIR setupFile (inStage irFile) (inStage cFile) leanPath leanir (stage.spawnArgs cfg)
    stage.finish outputs

/-- The module's output files, including those `lean` derives from the `.olean` path. -/
def Lean.ModuleArtifacts.outputs (arts : ModuleArtifacts) : Array FilePath :=
  #[arts.olean?, arts.oleanServer?, arts.oleanPrivate?, arts.ilean?,
    arts.irSig?, arts.ir?, arts.c?, arts.bc?].filterMap id

/-- Moves the output paths of `arts` into `dir`, keeping their file names. -/
def Lean.ModuleArtifacts.stageIn (arts : ModuleArtifacts) (dir : FilePath) : ModuleArtifacts :=
  let inDir := Option.map fun (p : FilePath) => dir / (p.fileName.getD "")
  { arts with
    olean? := inDir arts.olean?, oleanServer? := inDir arts.oleanServer?
    oleanPrivate? := inDir arts.oleanPrivate?, ilean? := inDir arts.ilean?
    irSig? := inDir arts.irSig?, ir? := inDir arts.ir?
    c? := inDir arts.c?, bc? := inDir arts.bc? }

def runLean
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String) (leanPath : SearchPath) (lean : FilePath)
  (wrap : IO.Process.SpawnArgs → IO.Process.SpawnArgs)
: LogIO Unit := do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then
    createParentDirs oleanFile
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then
    createParentDirs ileanFile
    args := args ++ #["-i", ileanFile.toString]
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      createParentDirs cFile
      args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then
    createParentDirs bcFile
    args := args ++ #["-b", bcFile.toString]
  createParentDirs setupFile
  IO.FS.writeFile setupFile (toJson setup).pretty
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  withLogErrorPos do
  let out ← rawProc <| wrap {
    args
    cmd := lean.toString
    env := #[
      ("LEAN_PATH", leanPath.toString)
    ]
  }
  let outLogPos ← getLogPos
  unless out.stdout.isEmpty do
    let txt ← out.stdout.split '\n' |>.foldM (init := "") fun (txt : String) ln => do
      let ln := ln.copy
      if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
        unless txt.isEmpty do
          logInfo s!"stdout:\n{txt}"
        let msg := {msg with fileName := mkRelPathString relLeanFile}
        logSerialMessage msg
        return txt
      else if txt.isEmpty && ln.isEmpty then
        return txt
      else
        return txt ++ ln ++ "\n"
    unless txt.isEmpty do
      logInfo s!"stdout:\n{txt}"
  unless out.stderr.isEmpty do
    logInfo s!"stderr:\n{out.stderr.trimAscii}"
  -- Elide the generic "Lean exited with code 1" when Lean already
  -- reported errors (the usual compiler-failure case). Keep it for other
  -- nonzero codes, for code 1 without diagnostics, and for the anomalous
  -- case where Lean logs errors but exits successfully.
  -- See https://github.com/leanprover/lean4/issues/10825
  let hasErrors := (← getLog).takeFrom outLogPos |>.any (·.level matches .error)
  if out.exitCode = 1 && hasErrors then
    failure
  else if out.exitCode ≠ 0 || hasErrors then
    error s!"Lean exited with code {out.exitCode}"

public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
: JobM Unit := withStage? fun
  | none => runLean leanFile relLeanFile setup setupFile arts leanArgs leanPath lean id
  | some (cfg, stage) => do
    let outputs := stageOutputs arts.outputs
    runLean leanFile relLeanFile setup setupFile (arts.stageIn stage.dir) leanArgs leanPath lean
      (stage.spawnArgs cfg)
    stage.finish outputs
