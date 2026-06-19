# Developer Guide: recommended Lean machinery

This page recommends the Lean tooling, libraries, and proof machinery to use when working
on LeaTTa. For the concepts themselves, read the [documentation](Home).

## Toolchain

- **elan** manages the Lean toolchain. The exact version is pinned in `lean-toolchain`
  (`leanprover/lean4:v4.31.0`); elan reads that file automatically.
- **lake** is the build tool. `lake build LeaTTa` builds just the interpreter binary,
  `lake build` builds everything including the metatheory, and `lake exe cache get`
  fetches prebuilt Mathlib oleans so you do not compile Mathlib yourself.
- **Editor:** VS Code with the Lean 4 extension, or any editor with the Lean LSP. The
  extension gives you the goal view, `exact?`, and hover types, which are the main way to
  drive proofs interactively.

## Libraries and the computability split

- **Mathlib** is pinned to the release whose toolchain matches ours. It backs the
  metatheory layer only, that is `MettaHyperonFull/Proofs/` and
  `MettaHyperonFull/Operational/`. Use it freely there for orders, `Multiset`,
  `Relation.ReflTransGen`, decidability infrastructure, and `aesop`.
- **The executable kernel does not import Mathlib.** `Multiset`, `Finset`, and `Real` are
  noncomputable, so the interpreter that must `lake exe` stays on `List` and
  `Std.HashMap`. Preserve this split: computable code under `Core`, `Runtime`, and
  `Minimal` stays Mathlib free, and proofs about it live under `Proofs`.

## Proof machinery we rely on

- `omega` for linear arithmetic over `Nat` and `Int`.
- `decide` and `Decidable` instances for finite, computable checks.
- `simp` with explicit lemma sets, rather than blanket simp, so proofs stay stable.
- `aesop` where a goal is routine.
- `termination_by` and `decreasing_by` for the fuel-bounded interpreter driver; the
  termination measure is explicit and Lean checks it.
- Hard invariant: zero `sorry`, zero `admit`, zero `native_decide`, zero `partial`, and
  zero `unsafe`. A proof that needs one of these is not finished.

## Finding lemmas

- `exact?`, `apply?`, and `rw?` suggest library lemmas from the current goal.
- For broader search, use Loogle, the Mathlib search, or a lemma-search MCP. Prefer an
  existing Mathlib lemma over a hand-rolled one in the proof layer.

## Module layout

- `MettaHyperonFull/Core` is the object language.
- `MettaHyperonFull/Runtime/Parser` parses surface MeTTa.
- `MettaHyperonFull/Minimal/Interpreter` and `Minimal/Stdlib` are the faithful kernel and
  the standard library written over its twelve instructions. This is the computable heart.
- `MettaHyperonFull/Proofs` is the Mathlib-backed metatheory: determinism, confluence of
  the deterministic fragment, sound and complete first-argument indexing, type soundness,
  and alpha-equivalence.
- `MettaHyperonFull/Operational` machine-checks the published Meta-MeTTa operational
  semantics: the four-register machine, its barbed bisimulation, and the gas extension.

## Contributing

See [CONTRIBUTING.md](https://github.com/MesTTo/LeaTTa/blob/metatheory/CONTRIBUTING.md).
Keep the kernel Mathlib free, put new theorems under `Proofs`, and validate behavior
against Hyperon's corpus with `make oracle` before proposing a change.
