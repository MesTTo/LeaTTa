#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

#
# Fail CI if the captured Lean/Lake build output contains warnings.
#
set -euo pipefail

log="${1:-build.log}"

if [ ! -r "$log" ]; then
  echo "Build log not readable: $log"
  exit 2
fi

hits=$(grep -nE '(^|[[:space:]])warning:' "$log" || true)

if [ -n "$hits" ]; then
  echo "Lean/Lake build warnings found in $log:"
  echo "$hits"
  exit 1
fi

echo "OK: no Lean/Lake build warnings in $log."
