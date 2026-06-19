#!/usr/bin/env bash
# Run every tests/regression/*.metta feature test through the interpreter and tally assertions.
# These guard the stdlib/grounded-op coverage added on top of the vendored Hyperon oracle.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/LeaTTa
[ -x "$BIN" ] || { echo "build first: lake build"; exit 1; }
tot_pass=0; tot_fail=0; rc=0
for f in tests/regression/*.metta; do
  out=$("$BIN" --oracle "$f" 2>&1 | tail -1)
  echo "$(basename "$f"): $out"
  p=$(echo "$out" | grep -oE 'PASS=[0-9]+' | grep -oE '[0-9]+' || echo 0)
  fl=$(echo "$out" | grep -oE 'FAIL=[0-9]+' | grep -oE '[0-9]+' || echo 0)
  tot_pass=$((tot_pass + p)); tot_fail=$((tot_fail + fl))
  [ "$fl" -ne 0 ] && rc=1
done
echo "---------------------------------------------"
echo "REGRESSION TOTAL: PASS=$tot_pass FAIL=$tot_fail"
[ $rc -eq 0 ] && echo "REGRESSION OK" || echo "REGRESSION FAILURES"
exit $rc
