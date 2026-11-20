/-!
A module that starts two background processes which outlive `lean` and prints their PIDs: a plain
child and a daemon in its own session, orphaned by its parent shell. Both are a `sleep` with an
unusual duration, so the test can recognise them, and end by themselves. Their standard streams
are closed, so they do not hold Lake's pipe from `lean` open.
-/

#eval show IO Unit from do
  let child ← IO.Process.spawn {
    cmd := "sleep", args := #["37.4242"], stdin := .null, stdout := .null, stderr := .null }
  IO.println s!"survivor pid {child.pid}"
  let out ← IO.Process.output {
    cmd := "sh", args := #["-c", "setsid sleep 37.4242 </dev/null >/dev/null 2>&1 & echo $!"] }
  IO.println s!"daemon pid {out.stdout.trimAscii}"
