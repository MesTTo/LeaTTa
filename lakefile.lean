import Lake
open Lake DSL

package «MettaHyperonFull» where
  version := v!"0.3.1"
  keywords := #["MeTTa", "Hyperon", "formal semantics", "metatheory", "verified interpreter"]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Mathlib backs the *metatheory layer only* (Multiset, Relation.ReflTransGen, order /
-- decidability infrastructure, aesop). Pinned to the release whose toolchain matches ours
-- (leanprover/lean4:v4.31.0). The executable kernel deliberately does NOT import it:
-- Multiset/Finset/Real are noncomputable, so the interpreter that must `lake exe` stays on
-- List / Std.HashMap. This split is about computability, not dependency purity.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib «MettaHyperonFull» where
  roots := #[`MettaHyperonFull]

-- Proofs ABOUT the kernel (determinism / result well-definedness, confluence of the
-- deterministic fragment, optimization-preservation, α-equivalence, type soundness).
-- A separate target so `LeaTTa` — the runnable binary, rooted at `Main` — never links
-- Mathlib.
@[default_target]
lean_lib «Metatheory» where
  roots := #[`MettaHyperonFull.Proofs]

-- The published Meta-MeTTa operational semantics (arXiv 2305.17218): the four-register abstract
-- machine, its barbed bisimulation, the resource-bounded (gas) extension, and the verified
-- on-chain guarantees (knowledge-base auditability, gas non-creation). A computable spec sharing
-- the `Core` object language with the kernel; a separate target so it is machine-checked in CI.
@[default_target]
lean_lib «Operational» where
  roots := #[`MettaHyperonFull.Operational]

-- The MeTTaIL formalization: F1R3FLY-io's Meta Type Talk Intermediate Language. A meta-language of
-- graph-structured lambda theories (presentations + the elaboration algebra), its type-lifting
-- transformation, the GSLT operational semantics, the hypercube typing, and the spice/mq-calculus
-- extensions. The computable core (data model, elaboration, transforms, reduction) is Mathlib-free,
-- like the kernel; a separate target so it is machine-checked in CI and the `LeaTTa` binary never
-- links it.
@[default_target]
lean_lib «MeTTaIL» where
  roots := #[`MeTTaIL]

-- Machine-checked sanity tests for the MeTTaIL formalization, kept out of the shipped library.
@[default_target]
lean_lib «MeTTaILTests» where
  roots := #[`MeTTaILTests]

@[default_target]
lean_exe «LeaTTa» where
  root := `Main
