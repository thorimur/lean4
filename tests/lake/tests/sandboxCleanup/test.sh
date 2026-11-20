#!/usr/bin/env bash
source ../common.sh

# Tests that deleting a stage cannot be redirected outside it, whatever links the sandboxed code
# leaves behind.
#
# Safety: everything this test writes is under its own `work/` directory. The data that a bug could
# delete is `work/decoy`, which the test creates for this purpose.

./clean.sh
copy_to_work lakefile.toml Links.lean Usurp.lean

echo "# TEST: invalid sandbox templates are rejected"
echo '{"command": []}' > template.json
test_err "must not be empty" build Links --sandbox template.json
echo '{"command": ["sandbox", "{stage}"]}' > template.json
test_err "must contain the element" build Links --sandbox template.json
echo '{"command": ["{command}", "{stage}"]}' > template.json
test_err "must start with the sandbox's program" build Links --sandbox template.json
echo '{"command": ["sandbox", "{command}", "{command}"]}' > template.json
test_err "only once" build Links --sandbox template.json

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
