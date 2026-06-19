/-
LeaTTa: Chapter: The Operational Semantics (MOPS).
-/
import VersoManual
import Illuminate
import Docs.Cd
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The Operational Semantics" =>
%%%
tag := "sec-operational"
%%%

Alongside the executable interpreter, LeaTTa formalizes the *published* operational semantics of
MeTTa; the four-register abstract machine of {citet mops}[], which its authors intend as MeTTa's
independent "JVM-specification". To our knowledge this is its first machine-checked rendering.

# The Four-Register Machine

A MOPS state is a tuple of four multiset registers `⟨i, k, w, o⟩`: an *input* register where queries
arrive, the *knowledge base* `k` (the atomspace), a *workspace* `w` for intermediate results, and an
*output* register `o`. These are multisets rather than lists because results are delivered in no
particular order, so the non-determinism is intrinsic to the state.

```diagram (cssWidth := "26em")
cd do
  let i ← CDM.node "i" cdInk
  let w ← CDM.node "w" cdInk
  let o ← CDM.node "o" cdInk
  let k ← CDM.node "k" cdPurple
  CDM.grid #[#[some i, some w, some o], #[some k, none, none]]
  CDM.arrow i w (some "QUERY/CHAIN") cdBlue .above
  CDM.arrow w o (some "OUTPUT") cdGreen .above
  CDM.arrow i k (some "ADD/REM") cdRed .left
```

The named small-step rules are formalized as an inductive `Step : State → State → Prop`
(`Operational/Semantics.lean`): *QUERY* reduces an input term against `k`'s equations, depositing all
matching instantiated right-hand sides into the workspace; *CHAIN* does the same for a workspace term;
*TRANSFORM* applies an explicit `transform`; *ADDATOM*/*REMATOM* mutate the knowledge base and emit
unit; and *OUTPUT* moves an irreducible (`insensitive`) workspace term to the output. The matcher
`unify` is the kernel's own `matchAtoms`, so the spec is wired to the same matcher the interpreter
runs.

# Verified Properties

LeaTTa proves three properties of this machine that matter directly for MeTTa's on-chain use:

 * *QUERY is sound and complete*: a workspace contractum is produced *iff* it is a genuine
   instantiated equation firing (`mem_equalityReductions`).
 * *The knowledge base is auditable*: a single step changes `k` only by an explicit
   `add-atom`/`remove-atom`; pure reduction never mutates it (`smallStep?_kb_auditable`). Every
   change to contract state is thus attributable.
 * *Gas is never created*: in the resource-bounded extension (effort tokens with a non-negative
   transition cost), total energy is monotonically non-increasing
   (`resourceStep?_energy_nonincreasing`). A contract can only ever *spend* gas.

# Program Equivalence: Barbed Bisimulation

Following {citet mops}[], program equality is *barbed bisimulation*: two states are equivalent when
they agree on every observable barb (input/workspace/output atoms) and every step of one is matched
by a step of the other back into the relation. LeaTTa defines this (`Operational/Bisimulation.lean`)
and proves bisimilarity is an *equivalence relation*, that is, reflexive, symmetric, and transitive (the
transitivity proof correctly composes the forward and backward simulations). The knowledge base is
internal and not observed, matching MOPS's coarse-grained treatment of the workspace.
