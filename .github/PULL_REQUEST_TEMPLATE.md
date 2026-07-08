<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

<!-- Thanks for contributing. CI runs all of the checks below on every pull request, and they must
     pass before a change can merge. You can run them locally first; see the commands beside each. -->

## What this changes

<!-- One or two plain sentences. -->

## Checklist

- [ ] `lake build` succeeds: the kernel, the `LeaTTa` binary, and the Mathlib metatheory.
- [ ] No `sorry`, `admit`, `native_decide`, `partial`, or `unsafe` in `MettaHyperonFull/`
      (`scripts/ci/check-no-forbidden.sh`).
- [ ] The differential oracle passes 270/270 (`make oracle`).
- [ ] The regression suite passes (`make regression`).
- [ ] New theorems keep their proofs under `Proofs/`, and the executable kernel stays Mathlib free.
- [ ] Prose and comments follow the house style: plain and direct, no em dashes, no commenting the
      obvious (see CONTRIBUTING.md).
