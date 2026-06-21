#!/usr/bin/env bash
#
# Write the README shipped inside a LeaTTa release bundle.
#
# Usage: scripts/write-release-readme.sh OUT_DIR VERSION PLATFORM
set -euo pipefail

OUT_DIR="${1:?output directory}"
VERSION="${2:?version}"
PLATFORM="${3:?platform}"

case "$PLATFORM" in
  windows*) BIN="bin/LeaTTa.exe" ;;
  *) BIN="bin/LeaTTa" ;;
esac

cat > "$OUT_DIR/README.md" <<EOF
# LeaTTa ${VERSION} (${PLATFORM})

This bundle contains the native LeaTTa executable and a small set of examples. The binary runs
without a Lean toolchain.

## Contents

- \`${BIN}\`: the executable minimal MeTTa interpreter and MeTTaIL runtime entry point.
- \`examples/*.metta\`: a representative slice of Hyperon's own test corpus.
- \`examples/bool.mettail\`: a tiny editable MeTTaIL dialect file.
- \`install.sh\`: installer for Unix-like bundles, when present.

## Quick Checks

Run the minimal interpreter:

    ${BIN} --min '!(+ 1 (* 2 (- 10 4)))'

Expected output:

    [13]

Run the MeTTaIL dialect fixture:

    ${BIN} --mettail examples/bool.mettail --term '(notOp tt)'

Expected output:

    ff

Run a corpus oracle file:

    ${BIN} --oracle examples/a1_symbols.metta

Expected tail:

    ==== PASS=7  FAIL=0  TOTAL=7 ====

## Install

On Linux and macOS:

    ./install.sh

That installs \`${BIN}\` to \`~/.local/bin\` by default. Pass a prefix to install elsewhere, for example
\`sudo ./install.sh /usr/local\`.

On Windows, run \`${BIN}\` from this directory or place it on your PATH.

## MeTTaIL Dialect Files

The \`--mettail\` mode accepts a small line-oriented format:

    sort Tm
    term tt : Tm
    term ff : Tm
    term notOp : Tm -> Tm
    rewrite notTt : (notOp tt) => ff
    rewrite notFf : (notOp ff) => tt

Blank lines and \`#\` comments are allowed. This format covers base-rewrite dialects and feeds the
checked MeTTaIL runtime path.
EOF
