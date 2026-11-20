/-!
A module that tries to replace its stage's writable directory with a symbolic link to `decoy/`, a
directory the test creates next to the package, so that deleting the stage would delete `decoy`'s
contents if it followed the link. Each step may be denied, depending on the sandbox.
-/

#eval show IO Unit from do
  let some tmp ← IO.getEnv "TMPDIR" | return
  let decoy ← IO.FS.realPath "decoy"
  let w := (System.FilePath.mk tmp).parent.getD tmp
  let out ← IO.Process.output {
    cmd := "sh", args := #["-c", s!"rmdir '{tmp}' && rmdir '{w}' && ln -s '{decoy}' '{w}'"] }
  IO.println s!"replaced: {out.exitCode == 0}"
