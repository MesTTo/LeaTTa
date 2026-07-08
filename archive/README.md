<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Archived exploratory modules

This directory holds earlier models that were built during the project's design exploration and then
set aside. They are kept for reference and for the record of how the design evolved. They are **not**
part of the faithful core, are **not** compiled by the build, and should not be read as part of the
verified development.

Each module here is an *approximation* rather than the faithful minimal-MeTTa semantics. The faithful,
machine-checked artifact is the minimal interpreter and its standard library under
`MettaHyperonFull/Minimal/`, together with the `Core`, `Operational`, and `Proofs` libraries.

## Contents

- `Runtime/` (`Evaluator`, `Program`, `CLI`): an earlier four-register, MeTTa-style runtime,
  superseded by the minimal interpreter, which is the faithful evaluator. The faithful parser
  remains in `MettaHyperonFull/Runtime/Parser.lean`.
- `Metagraph/`: executable approximations of categorical metagraph rewriting (SPO and DPO).
- `Reflection/`: quotation, self-modification, and an approximate Ruliad sketch.
- `StdLib/`: the earlier approximate standard-library surface, superseded by `Minimal/Stdlib`.
- `Interop/` and `MetaTheory/`: host and distributed-atomspace contracts and a well-formedness
  metatheory written over the earlier runtime.

To revisit any of these, move the module back under `MettaHyperonFull/` and restore its import.
