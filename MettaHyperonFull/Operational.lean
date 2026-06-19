/-
The **Meta-MeTTa operational semantics** (Meredith, Goertzel, Warrell & Vandervorst,
*Meta-MeTTa: an operational semantics for MeTTa*, arXiv 2305.17218) as a verified Lean library.

This is the published four-register abstract machine ⟨input, knowledge base, workspace, output⟩ that
the authors intend as MeTTa's independent specification. It is a *distinct* artifact from the
faithful minimal-MeTTa interpreter (`Minimal/Interpreter`): the kernel is the assembly language that
runs programs, whereas this is the small-step spec used to reason about program equivalence and
resource bounds. Both are computable and share the `Core` object language (atoms, `matchAtoms`,
`instantiate`, `Space`).

Modules:
  * `State`          — the four-register state (+ a `history` register for reflection).
  * `Semantics`      — the small-step relation `smallStep?` / `runFuel` (QUERY, CHAIN, TRANSFORM,
                       add/remove-atom, OUTPUT) and the equality-rule reducer.
  * `Minimal`        — the minimal-MeTTa instruction set (eval/chain/unify/cons/decons/…).
  * `Trace`          — execution traces (the observable history).
  * `Bisimulation`   — barbed bisimulation (MOPS §5) and the proof it is an **equivalence**.
  * `ResourceBounded`— the resource-bounded (gas) extension: effort tokens + cost-guarded steps.
  * `Properties`     — verified properties: QUERY sound+complete (`mem_equalityReductions`),
                       knowledge-base **auditability** (`smallStep?_kb_auditable`), and **gas is
                       never created** (`resourceStep?_energy_nonincreasing`) — the on-chain
                       guarantees MeTTa's smart-contract use needs.
-/
import MettaHyperonFull.Operational.State
import MettaHyperonFull.Operational.Semantics
import MettaHyperonFull.Operational.Minimal
import MettaHyperonFull.Operational.Trace
import MettaHyperonFull.Operational.Bisimulation
import MettaHyperonFull.Operational.ResourceBounded
import MettaHyperonFull.Operational.Properties
