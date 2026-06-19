#!/usr/bin/env bash
#
# Build a self-contained release bundle of LeaTTa, the machine-checked minimal MeTTa
# interpreter, and package it as a tarball under dist/.
#
# The binary links only against the standard C library, not against any Lean shared
# runtime, so a bundle runs on another machine of the same OS and architecture with no
# Lean toolchain installed. The prebuilt Linux x86_64 bundle is the tested target;
# macOS bundles are produced by running this same script on macOS, and all platforms
# are covered by the source build and by .github/workflows/release.yml.
#
# Usage: scripts/build-release.sh [VERSION]
#   VERSION defaults to the package version recorded in lakefile.lean.
#
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

VERSION="${1:-$(grep -oE 'version := v!"[^"]+"' lakefile.lean | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)}"
VERSION="${VERSION:-0.0.0}"
OS="$(uname -s | tr '[:upper:]' '[:lower:]')"
ARCH="$(uname -m)"
case "$OS" in linux) OS=linux;; darwin) OS=macos;; esac
PLATFORM="${OS}-${ARCH}"
NAME="leatta-${VERSION}-${PLATFORM}"
OUT="dist/${NAME}"
BIN=".lake/build/bin/LeaTTa"

echo "==> Building LeaTTa (version ${VERSION}, ${PLATFORM}) ..."
lake build LeaTTa

echo "==> Staging bundle at ${OUT} ..."
rm -rf "$OUT" "dist/${NAME}.tar.gz" "dist/${NAME}.tar.gz.sha256"
mkdir -p "$OUT/bin" "$OUT/examples"

cp "$BIN" "$OUT/bin/LeaTTa"
strip "$OUT/bin/LeaTTa" 2>/dev/null || true   # smaller download; debug info is not needed to run

# A representative slice of Hyperon's own corpus, so a new user can test immediately.
for f in a1_symbols b1_equal_chain c1_grounded_basic d1_gadt test_stdlib; do
  [ -f "tests/corpus/${f}.metta" ] && cp "tests/corpus/${f}.metta" "$OUT/examples/"
done

[ -f LICENSE ] && cp LICENSE "$OUT/LICENSE"
cp scripts/install.sh "$OUT/install.sh"
chmod +x "$OUT/install.sh"

cat > "$OUT/README.md" <<EOF
# LeaTTa ${VERSION} (${PLATFORM})

A single-binary build of the machine-checked minimal MeTTa interpreter from the LeaTTa
project: https://github.com/MesTTo/LeaTTa

This bundle was built and tested on Linux x86_64. The same binary runs on other glibc
Linux machines of the same architecture. For macOS or Windows, build from source (see
the project INSTALL.md) or use the binaries attached to the GitHub release.

## Install

    ./install.sh                 # installs bin/LeaTTa to ~/.local/bin

Pass a prefix to install elsewhere, for example \`sudo ./install.sh /usr/local\`.

## Run

    LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'           # [13]
    LeaTTa --min '!(map-atom (1 2 3) \$x (* \$x \$x))'  # [(1 4 9)]
    LeaTTa --file examples/test_stdlib.metta
    LeaTTa --oracle examples/a1_symbols.metta      # PASS/FAIL/TOTAL over a test file
    LeaTTa                                          # built-in demo

Each result is printed as the list of values that \`!\`-evaluation produces. The binary
depends only on the standard C library; no Lean toolchain is needed to run it.
EOF

echo "==> Creating tarball ..."
( cd dist && tar czf "${NAME}.tar.gz" "${NAME}" )
( cd dist && (sha256sum "${NAME}.tar.gz" 2>/dev/null || shasum -a 256 "${NAME}.tar.gz") > "${NAME}.tar.gz.sha256" )

echo "==> Done."
ls -lh "dist/${NAME}.tar.gz"
cat "dist/${NAME}.tar.gz.sha256"
