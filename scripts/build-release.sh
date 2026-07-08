#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

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
[ -f tests/mettail/bool.mettail ] && cp tests/mettail/bool.mettail "$OUT/examples/"

[ -f LICENSE ] && cp LICENSE "$OUT/LICENSE"
cp scripts/install.sh "$OUT/install.sh"
chmod +x "$OUT/install.sh"
scripts/write-release-readme.sh "$OUT" "$VERSION" "$PLATFORM"

echo "==> Creating tarball ..."
( cd dist && tar czf "${NAME}.tar.gz" "${NAME}" )
( cd dist && (sha256sum "${NAME}.tar.gz" 2>/dev/null || shasum -a 256 "${NAME}.tar.gz") > "${NAME}.tar.gz.sha256" )

echo "==> Done."
ls -lh "dist/${NAME}.tar.gz"
cat "dist/${NAME}.tar.gz.sha256"
