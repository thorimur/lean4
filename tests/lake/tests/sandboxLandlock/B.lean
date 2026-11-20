/-!
A module that does not import `A` but tries to overwrite `A`'s `.olean` during elaboration.
It reports whether the write succeeded instead of failing, so the build outcome alone does not
reveal whether the sandbox stopped it.
-/

#eval show IO Unit from do
  try
    IO.FS.writeFile ".lake/build/lib/lean/A.olean" "poisoned"
    IO.println "overwrite succeeded"
  catch _ =>
    IO.println "overwrite denied"
