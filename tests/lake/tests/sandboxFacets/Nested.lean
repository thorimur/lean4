/-!
A module that reports the stage its `lean` runs in (through `TMPDIR`) and tries to write into the
stage numbered `-0` under the same build key, which an enclosing `withStage?` of the same job
creates before `lean`'s own stage (`-1`).
-/

#eval show IO Unit from do
  let some tmp ← IO.getEnv "TMPDIR" | return
  IO.println s!"lean stage: {tmp}"
  let outer := tmp.replace "-1/w/tmp" "-0/w"
  try
    IO.FS.writeFile (System.FilePath.mk outer / "intruder.txt") "intruder"
    IO.println "intrusion succeeded"
  catch _ =>
    IO.println "intrusion denied"
