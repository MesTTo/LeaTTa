<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# LeaTTa

LeaTTa is a Lean 4 formalization of Hyperon's minimal MeTTa interpreter, the small
"assembly language" that the rest of MeTTa is built on, together with machine-checked
kernel metatheory, the published operational semantics, a distributed atomspace model,
MeTTaIL, and the Cordial Miners runtime presentation.

## Documentation

The textbook-style treatment is the LeaTTa book. It covers the object language, the
interpreter, the type system, the metatheory, the operational semantics and its
correspondence to the kernel, and the blockchain angle. Start there.

- **The book:** https://mestto.github.io/LeaTTa/
- **Repository and README:** https://github.com/MesTTo/LeaTTa
- **Install and run:** [INSTALL.md](https://github.com/MesTTo/LeaTTa/blob/metatheory/INSTALL.md)

This wiki keeps the short operational pages here. Everything broader is in the links above.

## Lean development

See the [Developer Guide](Developer-Guide) for the Lean toolchain, libraries, and proof
machinery to use when contributing to LeaTTa.

The [Mechanization Ledger](Mechanization-Ledger) maps public claims to checked Lean declarations. The
[Axiom Catalog](Axiom-Catalog) names the current assumption surface.
