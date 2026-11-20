#!/usr/bin/env bash
source ../common.sh

# Tests the Landlock sandboxes (`--sandbox=landlock` and `--sandbox=landlock-reap`).
#
# Safety: everything this test writes is under its own `work/` directory. It only probes processes
# (`kill -0`), except that it kills a leftover `sleep 37.4242` it started itself, after checking
# the command line of that PID. That `sleep` also ends by itself.

if [ "$UNAME" != Linux ]; then
  echo "SKIP: Landlock is Linux-only"
  exit 0
fi
RUNNER=$(command -v lake-sandbox-run || true)
if [ -z "$RUNNER" ]; then
  echo "SKIP: lake-sandbox-run not found"
  exit 0
fi

./clean.sh
copy_to_work lakefile.toml A.lean B.lean Spawn.lean
mkdir stage

if ! "$RUNNER" "$PWD/stage" -- true; then
  echo "SKIP: Landlock (ABI >= 3) is unavailable"
  exit 0
fi

MARKER="sleep 37.4242"
# The PID printed by `Spawn` after `$1 pid`, if that process still runs the marked `sleep`
marked_pid() {
  [ -f produced.out ] || return 0
  pid=$(sed -n "s/.*$1 pid \([0-9]*\).*/\1/p" produced.out | tail -n 1)
  if [ -n "$pid" ] && [ "$(ps -o args= -p "$pid" 2>/dev/null)" = "$MARKER" ]; then
    echo "$pid"
  fi
}
kill_survivors() {
  for label in survivor daemon; do
    pid=$(marked_pid $label)
    if [ -n "$pid" ]; then kill "$pid"; fi
  done
}
trap kill_survivors EXIT

echo "# TEST: the runner confines writes to its directory"
test_cmd "$RUNNER" "$PWD/stage" -- sh -c 'echo ok > stage/inside'
test_exp -f stage/inside
test_cmd_fails "$RUNNER" "$PWD/stage" -- sh -c 'echo bad > outside'
test_exp ! -f outside
test_cmd_fails "$RUNNER" "$PWD/stage" -- truncate -s 0 lakefile.toml
test_exp -s lakefile.toml
test_cmd "$RUNNER" "$PWD/stage" -- sh -c 'echo ok > /dev/null'

echo "# TEST: the runner fails closed without running the command"
test_cmd_fails "$RUNNER" "$PWD/missing" -- touch ran
test_exp ! -f ran
test_cmd_fails "$RUNNER" --reap "$PWD/missing" -- touch ran
test_exp ! -f ran

for SANDBOX in landlock landlock-reap; do
  rm -rf .lake
  echo "# TEST: $SANDBOX: another module's output cannot be overwritten"
  test_run build A --sandbox $SANDBOX
  cp .lake/build/lib/lean/A.olean A.olean.orig
  test_out "overwrite denied" build B --sandbox $SANDBOX
  test_cmd cmp -s .lake/build/lib/lean/A.olean A.olean.orig
done

echo "# TEST: landlock: background processes outlive lean"
test_out "daemon pid" build Spawn --sandbox landlock
test_exp -n "$(marked_pid survivor)"
test_exp -n "$(marked_pid daemon)"
kill_survivors

echo "# TEST: landlock-reap: no background process outlives lean, even a daemon"
rm -rf .lake
test_out "daemon pid" build Spawn --sandbox landlock-reap
test_exp -z "$(marked_pid survivor)"
test_exp -z "$(marked_pid daemon)"

# Cleanup
rm -f produced.out
