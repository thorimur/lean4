/-!
A module that leaves symbolic and hard links to `decoy/`, a directory the test creates next to the
package, in its stage's scratch directory, so that deleting the stage would delete `decoy`'s
contents if it followed them. Each step may be denied, depending on the sandbox.
-/

#eval show IO Unit from do
  let some tmp ← IO.getEnv "TMPDIR" | return
  let decoy ← IO.FS.realPath "decoy"
  let sh (cmd : String) : IO Unit := discard <| IO.Process.output {cmd := "sh", args := #["-c", cmd]}
  sh s!"ln -s '{decoy}' '{tmp}/dir-link'"
  sh s!"ln -s '{decoy}/keep' '{tmp}/file-link'"
  sh s!"mkdir -p '{tmp}/sub' && ln -s '{decoy}' '{tmp}/sub/dir-link'"
  sh s!"ln '{decoy}/keep' '{tmp}/hard-link'"
  let entries ← (System.FilePath.mk tmp).readDir
  IO.println s!"links: {(entries.map (·.fileName)).qsort (· < ·)}"
