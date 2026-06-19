#!/usr/bin/env bash
#
# Install the LeaTTa binary from a release bundle into a bin directory on your PATH.
# This script lives at the root of an unpacked release archive, next to bin/LeaTTa
# and examples/. It works on Linux and macOS. On Windows, build from source (see the
# project INSTALL.md).
#
# Usage: ./install.sh [PREFIX]
#   PREFIX defaults to $HOME/.local, so the binary lands in $HOME/.local/bin.
#   Pass /usr/local (with sudo) for a system-wide install.
#
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PREFIX="${1:-$HOME/.local}"
DEST="$PREFIX/bin"

if [ ! -x "$HERE/bin/LeaTTa" ]; then
  echo "error: $HERE/bin/LeaTTa not found. Run this from an unpacked release bundle." >&2
  exit 1
fi

mkdir -p "$DEST"
install -m 0755 "$HERE/bin/LeaTTa" "$DEST/LeaTTa"
echo "Installed LeaTTa to $DEST/LeaTTa"

case ":$PATH:" in
  *":$DEST:"*) ;;
  *)
    echo
    echo "Note: $DEST is not on your PATH. Add it, for example:"
    echo "  echo 'export PATH=\"$DEST:\$PATH\"' >> ~/.bashrc && source ~/.bashrc"
    ;;
esac

echo
echo "Test it:"
echo "  LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'            # [13]"
if [ -f "$HERE/examples/a1_symbols.metta" ]; then
  echo "  LeaTTa --oracle $HERE/examples/a1_symbols.metta"
fi
