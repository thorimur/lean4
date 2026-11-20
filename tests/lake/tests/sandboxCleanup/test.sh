#!/usr/bin/env bash
source ../common.sh

# Tests that deleting a stage cannot be redirected outside it, whatever links the sandboxed code
# leaves behind.
#
# Safety: everything this test writes is under its own `work/` directory. The data that a bug could
# delete is `work/decoy`, which the test creates for this purpose.

./clean.sh
copy_to_work lakefile.toml Links.lean Usurp.lean

echo "# TEST: an empty sandbox command is rejected"
echo '{"command": []}' > empty.json
test_err "must not be empty" build Links --sandbox empty.json

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
fi
if [ ${#SANDBOXES[@]} = 0 ]; then
  echo "SKIP: no supported sandbox available"
  exit 0
fi

for SANDBOX in "${SANDBOXES[@]}"; do
  echo "# TEST: $SANDBOX: deleting the stage leaves the decoy intact"
  rm -rf .lake decoy
  mkdir decoy
  echo keep > decoy/keep
  # `Usurp` fails to build if it manages to replace its writable directory
  lake_out build Links Usurp --sandbox $SANDBOX || true
  match_text "links:" produced.out
  if [ $SANDBOX != seatbelt ]; then
    # These sandboxes deny replacing the writable directory, so the stage is deleted
    match_text "replaced: false" produced.out
    test_exp -z "$(ls -A .lake/build/stage)"
  fi
  test_exp -d decoy -a ! -L decoy
  test_cmd_eq keep cat decoy/keep
done

# Cleanup
rm -f produced.out
