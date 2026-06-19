/-
MeTTa / OpenCog Hyperon in Lean 4.

ARCHITECTURE. The minimal MeTTa interpreter (`Minimal/Interpreter`) is the assembly language of
MeTTa, the faithful core. The standard library (`Minimal/Stdlib`) is written as MeTTa over those
twelve instructions, exactly as in Hyperon. This is the active, validated artifact: it agrees with
Hyperon's own oracle `lib/tests/test_stdlib.metta` (see `IMPROVEMENTS_OVER_HYPERON.md`).

`Operational.*` is a separate, machine-checked library (its own `lean_lib «Operational»` target,
rooted at `MettaHyperonFull.Operational`): the published Meta-MeTTa operational semantics
(arXiv 2305.17218), namely the four-register abstract machine ⟨i,k,w,o⟩, its barbed bisimulation, the
resource-bounded (gas) extension, and the verified on-chain guarantees (knowledge-base auditability
and gas non-creation). It shares `Core` with the kernel but is a specification for reasoning about
MeTTa, distinct from and not imported by the runnable faithful core here.

Earlier exploratory models live under `archive/` at the repository root. They are kept for reference,
are not built, and are deliberately not part of the faithful core, because each is an approximation
rather than the faithful minimal-MeTTa semantics. See `archive/README.md`.
-/

-- Faithful foundation: the object language the assembly is built on.
import MettaHyperonFull.Core.Atom
import MettaHyperonFull.Core.Pretty
import MettaHyperonFull.Core.Result
import MettaHyperonFull.Core.Bindings
import MettaHyperonFull.Core.Substitution
import MettaHyperonFull.Core.Alpha
import MettaHyperonFull.Core.FreeVars
import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.Matching
import MettaHyperonFull.Core.Space
import MettaHyperonFull.Core.Types
import MettaHyperonFull.Core.Grounding
import MettaHyperonFull.Core.Builtins

-- Parser: text to atoms.
import MettaHyperonFull.Runtime.Parser

-- The faithful core: minimal MeTTa interpreter (assembly) plus the stdlib written over it.
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Minimal.Stdlib

-- `Operational.*` is its own verified `lean_lib «Operational»` target; see the header above.
