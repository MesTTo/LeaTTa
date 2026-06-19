#!/usr/bin/env bash
#
# Reproducible oracle. Runs the minimal-MeTTa interpreter (`metta_full --oracle`)
# over Hyperon's own test corpus, vendored under tests/corpus/ (MIT, commit 3f76dc4), and checks
# every `!`-assertion against the
# expected results in tests/corpus/EXPECTED.txt.
#
# An assertion passes iff it evaluates to the unit atom `()`. Exit status is 0
# iff every file matches its expected PASS/FAIL/TOTAL — so this doubles as a
# regression gate (`scripts/run-oracle.sh && echo OK`).
#
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

CORPUS="tests/corpus"
EXPECTED="$CORPUS/EXPECTED.txt"
BIN=".lake/build/bin/metta_full"

echo "Building metta_full ..."
if ! lake build metta_full >/dev/null 2>&1; then
  echo "BUILD FAILED"; exit 2
fi

fail=0; tot_pass=0; tot_total=0; nfiles=0
printf "%-26s %6s %6s %6s   %s\n" FILE PASS FAIL TOTAL STATUS
while read -r file ep ef et; do
  case "$file" in ''|\#*) continue;; esac
  out=$(timeout 120 "$BIN" --oracle "$CORPUS/$file" 2>/dev/null \
        | grep -oE 'PASS=[0-9]+  FAIL=[0-9]+  TOTAL=[0-9]+')
  p=$(printf '%s' "$out" | grep -oE 'PASS=[0-9]+'  | grep -oE '[0-9]+'); p=${p:-X}
  f=$(printf '%s' "$out" | grep -oE 'FAIL=[0-9]+'  | grep -oE '[0-9]+'); f=${f:-X}
  t=$(printf '%s' "$out" | grep -oE 'TOTAL=[0-9]+' | grep -oE '[0-9]+'); t=${t:-X}
  if [ "$p" = "$ep" ] && [ "$f" = "$ef" ] && [ "$t" = "$et" ]; then
    status="ok"
  else
    status="MISMATCH (expected $ep/$ef/$et)"; fail=1
  fi
  printf "%-26s %6s %6s %6s   %s\n" "$file" "$p" "$f" "$t" "$status"
  if [ "$p" != "X" ]; then tot_pass=$((tot_pass+p)); tot_total=$((tot_total+t)); nfiles=$((nfiles+1)); fi
done < "$EXPECTED"

echo "---------------------------------------------------------------------"
echo "TOTAL: $tot_pass / $tot_total assertions pass across $nfiles files"
if [ "$fail" = 0 ]; then
  echo "ORACLE OK — every file matches tests/corpus/EXPECTED.txt"
else
  echo "ORACLE MISMATCH — see rows marked MISMATCH above"
fi
exit $fail
