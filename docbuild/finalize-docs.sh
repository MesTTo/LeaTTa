#!/usr/bin/env bash
#
# Trim the doc-gen4 output for hosting. The full reference includes Mathlib, whose pages
# are about 1 GB, over the GitHub Pages limit. Rewrite links into Mathlib so they point at
# the official mathlib4_docs site, then drop the local Mathlib tree. The project's own
# pages and the Lean core references (Init, Std, Lean, Lake, Batteries) stay local.
#
# Usage: docbuild/finalize-docs.sh [DOC_DIR]   (default: .lake/build/doc)
#
set -euo pipefail
DOC="${1:-.lake/build/doc}"
MATHLIB_DOCS="https://leanprover-community.github.io/mathlib4_docs/Mathlib"

find "$DOC" -name '*.html' -exec sed -i -E \
  "s#(href=\")((\.\./|\./)+)Mathlib(/|\.html)#\1${MATHLIB_DOCS}\4#g" {} +

rm -rf "$DOC/Mathlib"

echo "Finalized API docs: Mathlib links retargeted to mathlib4_docs, local Mathlib tree removed."
du -sh "$DOC"
