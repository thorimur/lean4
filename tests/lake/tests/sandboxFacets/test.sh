#!/usr/bin/env bash
source ../common.sh

# Tests that custom targets and facets get build stages: a target that opts in with `withStage?`,
# a module facet that calls `compileLeanModule` itself, and one that does so inside a stage of its
# own, nesting two stages. Also checks that a sandboxed command gets its working directory and
# environment changes, exactly as it would unsandboxed.
#
# Safety: everything this test writes is under its own `work/` directory.

./clean.sh
copy_to_work lakefile.lean A.lean B.lean Nested.lean
OLEAN=.lake/build/lib/lean/A.olean
mkdir sub

# What `reportEnv` should log: `BAR` is set for Lake but unset for the command
SUB=$(cd sub && pwd -P)
EXPECTED_INHERIT=$(printf 'cwd=%s\nFOO=foo-value\nBAR=unset\nHOME=%s' "$SUB" "$HOME")
EXPECTED_CLEAR=$(printf 'cwd=%s\nFOO=foo-value\nBAR=unset\nHOME=unset' "$SUB")
report() {
  if ! BAR=from-lake "$LAKE" build "$@" > report.log 2>&1; then
    cat report.log
    return 1
  fi
  sed -n 's/.*report //p' report.log
}
check_reports() {
  echo "# TEST: $1: the command gets its working directory and environment"
  test_exp "$(report envInherit "${@:2}")" = "$EXPECTED_INHERIT"
  test_exp "$(report envClear "${@:2}")" = "$EXPECTED_CLEAR"
}
check_reports unsandboxed

echo "# TEST: unsandboxed, the custom target and facet run unconfined"
test_run build customTarget
test_cmd_eq unconfined cat .lake/build/customTarget.txt
test_run build A
cp $OLEAN A.olean.orig
test_out "overwrite succeeded" build +B:customOlean
test_cmd_fails cmp -s $OLEAN A.olean.orig

SANDBOXES=()
if [ "$UNAME" = Darwin ]; then
  SANDBOXES+=(seatbelt)
elif [ "$UNAME" = Linux ]; then
  if command -v bwrap > /dev/null; then SANDBOXES+=(bwrap); fi
  RUNNER=$(command -v lake-sandbox-run || true)
  mkdir probe
  if [ -n "$RUNNER" ] && "$RUNNER" "$PWD/probe" -- true; then
    SANDBOXES+=(landlock landlock-reap)
  fi
  WRITES=write-file,remove-dir,remove-file,make-char,make-dir,make-reg,make-sock,make-fifo
  WRITES=$WRITES,make-block,make-sym,refer,truncate
  if setpriv --nnp --landlock-access "fs:$WRITES" -- true 2>/dev/null; then
    SANDBOXES+=(landlock-setpriv)
  fi
fi
if [ ${#SANDBOXES[@]} = 0 ]; then
  echo "SKIP: no supported sandbox available"
  exit 0
fi

for SANDBOX in "${SANDBOXES[@]}"; do
  rm -rf .lake escaped.txt
  check_reports $SANDBOX --sandbox $SANDBOX

  echo "# TEST: $SANDBOX: a custom target's process is confined to its own stage"
  test_out "escape denied" build customTarget --sandbox $SANDBOX
  match_text "stage owner: test/customTarget" produced.out
  test_exp ! -f escaped.txt
  test_exp -f .lake/build/customTarget.txt.hash
  test_exp -z "$(ls -A .lake/build/stage)"
  test_cmd_eq staged cat .lake/build/customTarget.txt

  echo "# TEST: $SANDBOX: a custom facet calling compileLeanModule is sandboxed"
  test_run build A
  cp $OLEAN A.olean.orig
  test_out "overwrite denied" build +B:customOlean --sandbox $SANDBOX
  test_exp -f .lake/build/custom/B.olean
  test_exp -z "$(ls -A .lake/build/stage)"
  test_cmd cmp -s $OLEAN A.olean.orig

  echo "# TEST: $SANDBOX: nested stages are separate, and each has a single writer"
  test_out "intrusion denied" build +Nested:nestedOlean --sandbox $SANDBOX
  outer=$(sed -n 's/.*outer stage: \(.*\)$/\1/p' produced.out)
  inner=$(sed -n 's/.*lean stage: \(.*\)\/tmp$/\1/p' produced.out)
  echo "outer stage: $outer"
  echo "lean stage: $inner"
  test_exp -n "$outer" -a -n "$inner"
  # A stage is named after its key, followed by the key's hash and a counter
  if ! echo "$outer" | grep -Eq '/test__Nested_nestedOlean-[0-9a-f]{16}-0/w$'; then
    echo "FAILURE: unexpected stage name: $outer"
    exit 1
  fi
  test_exp "${outer%-0/w}" = "${inner%-1/w}" -a "$outer" != "$inner"
  test_exp -f .lake/build/nested/Nested.olean -a -f .lake/build/nested/outer.txt
  test_exp -z "$(ls -A .lake/build/stage)"
done

# Cleanup
rm -f produced.out
