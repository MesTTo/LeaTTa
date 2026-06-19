#!/usr/bin/env bash
#
# Static guard for the project invariant: the active development uses no sorry, admit, native_decide,
# partial, or unsafe. Covers the MeTTa kernel/metatheory (MettaHyperonFull/) and the MeTTaIL
# formalization (MeTTaIL/, MeTTaILProofs/, MeTTaILTests/ and their library roots). The archive/ tree
# is exploratory and excluded.
#
# This is a static check. It strips line comments and backtick-quoted mentions (our docstrings say
# things like "no `sorry`") so only real Lean uses are flagged. The CI also greps the build log for
# Lean's own "declaration uses 'sorry'" warning, which is the authoritative check for sorry/admit.
#
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

TARGETS="MettaHyperonFull MeTTaIL MeTTaILProofs MeTTaILTests MeTTaIL.lean MeTTaILProofs.lean MeTTaILTests.lean"

hits=$(grep -rnE '\b(sorry|admit|native_decide)\b|\b(partial|unsafe)[[:space:]]+(def|instance|abbrev|theorem|lemma|structure|inductive)\b' \
        $TARGETS --include='*.lean' 2>/dev/null \
       | grep -vE '`[^`]*`' \
       | grep -vE ':[0-9]+:[[:space:]]*(--|/-)' \
       | grep -vE '/--' \
       || true)

if [ -n "$hits" ]; then
  echo "FORBIDDEN placeholders found (sorry/admit/native_decide/partial/unsafe):"
  echo "$hits"
  exit 1
fi
echo "OK: no forbidden placeholders in MettaHyperonFull/ or the MeTTaIL formalization."
