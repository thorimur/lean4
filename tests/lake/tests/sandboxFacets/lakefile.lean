import Lake
open System Lake DSL

package test

lean_lib A
lean_lib B
lean_lib Nested

/--
A custom target that opts into a build stage itself: its process writes its output to the stage
and tries to write outside it. Without a sandbox, it writes its output directly.
-/
target customTarget pkg : FilePath := Job.async do
  let installed := pkg.buildDir / "customTarget.txt"
  withStage? fun
  | none => do
    createParentDirs installed
    IO.FS.writeFile installed "unconfined\n"
    return installed
  | some (cfg, stage) => do
    logInfo s!"stage key: {stage.key}"
    -- The name under which the sandboxed process writes the output in the stage
    let inStage := "output.txt"
    let escape := pkg.dir / "escaped.txt"
    let out ← IO.Process.output <| stage.spawnArgs cfg {
      cmd := "sh"
      args := #["-c", s!"echo staged > '{stage.dir / inStage}'; \
        (echo escaped > '{escape}') 2>/dev/null && echo 'escape succeeded' || echo 'escape denied'"] }
    logInfo out.stdout
    stage.finish #[(inStage, installed)]
    return installed

/-- A custom module facet that elaborates the module by calling `compileLeanModule` itself. -/
module_facet customOlean mod : FilePath := Job.async do
  let dir := mod.pkg.buildDir / "custom"
  let olean := dir / s!"{mod.name}.olean"
  compileLeanModule mod.leanFile mod.leanFile {name := mod.name} (dir / s!"{mod.name}.setup.json")
    {olean? := olean} (leanPath := ← getLeanPath) (lean := ← getLean)
  return olean

/--
A custom module facet that runs a process in a stage of its own and, inside it, calls
`compileLeanModule`, which opens a second stage for `lean`.
-/
module_facet nestedOlean mod : FilePath := Job.async do
  let dir := mod.pkg.buildDir / "nested"
  let olean := dir / s!"{mod.name}.olean"
  let compile := compileLeanModule mod.leanFile mod.leanFile {name := mod.name}
    (dir / s!"{mod.name}.setup.json") {olean? := olean} (leanPath := ← getLeanPath)
    (lean := ← getLean)
  withStage? fun
  | none => compile
  | some (cfg, outer) => do
    logInfo s!"outer stage: {outer.dir}"
    let inStage := "outer.txt"
    discard <| IO.Process.output <| outer.spawnArgs cfg {
      cmd := "sh", args := #["-c", s!"echo outer > '{outer.dir / inStage}'"] }
    compile
    outer.finish #[(inStage, dir / "outer.txt")]
  return olean
