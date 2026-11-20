/-!
A module that writes a scratch file to `TMPDIR` and, if `LAKE_TEST_LITTER` is set, a file
next to its outputs in its stage, which Lake must reject.
-/

#eval show IO Unit from do
  if let some tmp ← IO.getEnv "TMPDIR" then
    IO.FS.writeFile (System.FilePath.mk tmp / "scratch") "ok"
    if (← IO.getEnv "LAKE_TEST_LITTER").isSome then
      IO.FS.writeFile (System.FilePath.mk tmp / ".." / "litter") "unexpected"
