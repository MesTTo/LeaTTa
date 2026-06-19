#!/usr/bin/env bash
#
# Static guard for the project invariant: the active development under MettaHyperonFull/ uses no
# sorry, admit, native_decide, partial, or unsafe. The archive/ tree is exploratory and excluded.
#
# This is a static check. It strips line comments and backtick-quoted mentions (our docstrings say
# things like "no `sorry`") so only real Lean uses are flagged. The CI also greps the build log for
# Lean's own "declaration uses 'sorry'" warning, which is the authoritative check for sorry/admit.
#
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

hits=$(grep -rnE '\b(sorry|admit|native_decide)\b|\b(partial|unsafe)[[:space:]]+(def|instance|abbrev|theorem|lemma|structure|inductive)\b' \
        MettaHyperonFull --include='*.lean' 2>/dev/null \
       | grep -vE '`[^`]*`' \
       | grep -vE ':[0-9]+:[[:space:]]*(--|/-)' \
       | grep -vE '/--' \
       || true)

if [ -n "$hits" ]; then
  echo "FORBIDDEN placeholders found in MettaHyperonFull/ (sorry/admit/native_decide/partial/unsafe):"
  echo "$hits"
  exit 1
fi
echo "OK: no forbidden placeholders in MettaHyperonFull/"
