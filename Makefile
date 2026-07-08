# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

# Convenience targets for the LeaTTa MeTTa interpreter.
# `lake` does the real work; these are thin wrappers for common tasks.

LEAN_BIN := .lake/build/bin/LeaTTa
PREFIX   ?= $(HOME)/.local

.PHONY: build all release install uninstall test oracle regression clean

build:            ## Build just the interpreter binary
	lake build LeaTTa

all:              ## Build the kernel, the binary, and the Mathlib metatheory
	lake build

release:          ## Package a self-contained tarball under dist/
	scripts/build-release.sh

install: build    ## Install the binary into $(PREFIX)/bin
	install -d $(PREFIX)/bin
	install -m 0755 $(LEAN_BIN) $(PREFIX)/bin/LeaTTa
	@echo "Installed LeaTTa to $(PREFIX)/bin/LeaTTa"

uninstall:        ## Remove an installed binary from $(PREFIX)/bin
	rm -f $(PREFIX)/bin/LeaTTa

oracle: build     ## Differential oracle against Hyperon's corpus
	scripts/run-oracle.sh

regression: build ## Stdlib and grounded-op feature tests
	scripts/run-regression.sh

test: oracle regression  ## Run the full validation suite

clean:            ## Remove release artifacts (keeps the Lean build cache)
	rm -rf dist
