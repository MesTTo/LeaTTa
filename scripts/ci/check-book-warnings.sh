#!/usr/bin/env bash
#
# Fail CI if the Verso book build emits any warning except the reviewed upstream warning in
# Verso v4.31.0.
#
set -euo pipefail

log="${1:-book-build.log}"

if [ ! -r "$log" ]; then
  echo "Book build log not readable: $log"
  exit 2
fi

hits=$(grep -nE '(^|[[:space:]])warning:' "$log" || true)

if [ -z "$hits" ]; then
  echo "OK: no Lean/Lake book warnings in $log."
  exit 0
fi

known_pattern='VersoManual/Docstring\.lean:1535:2: .*@\[expose\].*has no effect outside.*module.*file'
unknown=$(printf '%s\n' "$hits" | grep -vE "$known_pattern" || true)

if [ -n "$unknown" ]; then
  echo "Unreviewed Lean/Lake book warnings found in $log:"
  echo "$unknown"
  exit 1
fi

echo "OK: only the reviewed upstream Verso v4.31.0 warning appears in $log."
