#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

#
# Static guard for the project invariant: the active development uses no sorry, admit, native_decide,
# partial, or unsafe. Covers the MeTTa kernel/metatheory, the MeTTaIL formalization, and the Cordial
# Miners formalization. The archive/ tree is exploratory and excluded.
#
# This is a static check. It strips line comments and backtick-quoted mentions (our docstrings say
# things like "no `sorry`") so only real Lean uses are flagged. The CI also fails on every Lean/Lake
# build warning through scripts/ci/check-build-warnings.sh.
#
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

TARGETS="MettaHyperonFull MeTTaIL MeTTaILProofs MeTTaILTests MeTTaIL.lean MeTTaILProofs.lean MeTTaILTests.lean CordialMiners CordialMiners.lean"

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
echo "OK: no forbidden placeholders in MettaHyperonFull/, MeTTaIL/, MeTTaILProofs/, MeTTaILTests/, or CordialMiners/."
