#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Tests `--sandbox`: `lean` may write only to its stage, and Lake installs only expected outputs.

if [ "$UNAME" = Darwin ]; then
  SANDBOX=seatbelt
elif command -v bwrap > /dev/null; then
  SANDBOX=bwrap
else
  echo "SKIP: no supported sandbox available"
  exit 0
fi

copy_to_work lakefile.toml A.lean B.lean Litter.lean Mod.lean ModEager.lean
OLEAN=.lake/build/lib/lean/A.olean

echo "# TEST: unsandboxed, a module can overwrite another module's outputs"
test_run build A
cp $OLEAN A.olean.orig
test_out "overwrite succeeded" build B
test_cmd_fails cmp -s $OLEAN A.olean.orig
rm -rf .lake

echo "# TEST: sandboxed, the overwrite is denied"
test_run build A --sandbox $SANDBOX
cp $OLEAN A.olean.orig
test_out "overwrite denied" build B --sandbox $SANDBOX
test_cmd cmp -s $OLEAN A.olean.orig

echo "# TEST: sandboxed outputs are recorded consistently"
test_run build A B --no-build
test_run build A B --no-build --rehash
test_exp -z "$(ls -A .lake/build/stage)"

echo "# TEST: scratch files in TMPDIR are discarded"
test_run build Litter --sandbox $SANDBOX
test_exp -f .lake/build/lib/lean/Litter.olean

echo "# TEST: unexpected files in the stage fail the build"
rm -rf .lake/build/lib/lean/Litter.*
LAKE_TEST_LITTER=1 test_err "unexpected entry 'litter'" build Litter --sandbox $SANDBOX
test_exp ! -f .lake/build/lib/lean/Litter.olean
test_exp -z "$(ls -A .lake/build/stage)"

echo "# TEST: module-system outputs, from \`lean\` and from \`leanir\`, are installed"
test_run build +Mod:c +ModEager:c --sandbox $SANDBOX
for m in Mod ModEager; do
  for ext in olean olean.server olean.private ilean ir ir.sig; do
    test_exp -f .lake/build/lib/lean/$m.$ext
    test_exp -f .lake/build/lib/lean/$m.$ext.hash
  done
  test_exp -f .lake/build/ir/$m.c
done
test_run build +Mod:c +ModEager:c --no-build
test_exp -z "$(ls -A .lake/build/stage)"

echo "# TEST: a sandbox given by a JSON template"
if [ "$SANDBOX" = seatbelt ]; then
  cat > template.json <<'JSON'
{"command": ["sandbox-exec", "-D", "STAGE={stage}", "-p",
  "(version 1)(allow default)(deny file-write*)(allow file-write* (subpath (param \"STAGE\")) (literal \"/dev/null\"))",
  "{command}"]}
JSON
else
  cat > template.json <<'JSON'
{"command": ["bwrap", "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc",
  "--bind", "{stage}", "{stage}", "--unshare-pid", "--die-with-parent", "--", "{command}"]}
JSON
fi
rm -rf .lake
test_run build A
cp $OLEAN A.olean.orig
test_out "overwrite denied" build B --sandbox template.json
test_cmd cmp -s $OLEAN A.olean.orig

# Cleanup
rm -f produced.out
