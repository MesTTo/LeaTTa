-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/- jscpd:ignore-start -/
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
/- jscpd:ignore-end -/

Alongside the executable interpreter, LeaTTa formalizes the published operational semantics of MeTTa: the
four-register abstract machine of {citet mops}[], which its authors describe as an independent
specification of the language. I have not found an earlier machine-checked rendering.

# The Four-Register Machine

A MOPS state is a four-register tuple `⟨i, k, w, o⟩`. Each register has a role:

 * `i` is the *input* register, where queries arrive.
 * `k` is the *knowledge base* (the atomspace).
 * `w` is the *workspace*, used for intermediate results.
 * `o` is the *output* register.

All four are multisets, because results are delivered in no particular order and the non-determinism is intrinsic to the state.

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

The small-step semantics is a computable function `smallStep?` (`Operational/Semantics.lean`) that
returns the next state tagged with a `StepKind`. Each kind has one job:

 * *QUERY*: reduces an input term against `k`'s equations, depositing all matching instantiated
   right-hand sides into the workspace. A `transform` atom reduces under QUERY, not as a separate step.
 * *CHAIN*: does the same for a workspace term.
 * *ADDATOM* / *REMATOM*: consume the matched input command, mutate the knowledge base, and emit unit.
 * *OUTPUT*: moves an irreducible (`insensitive`) workspace term to the output.

The matcher used is the kernel's own `matchAtoms`, so the spec is wired to the same matcher the interpreter runs.

# Verified Properties

LeaTTa proves three properties of this machine:

 * *QUERY is sound and complete*: a workspace contractum is produced exactly when it is a genuine
   instantiated equation firing (`mem_equalityReductions`).
 * *The knowledge base is auditable*: a single step changes `k` only by an explicit
   `add-atom`/`remove-atom`. Pure reduction never mutates it (`smallStep?_kb_auditable`).
 * *Gas is never created*: in the resource-bounded extension, with effort tokens and a non-negative
   transition cost, total energy is monotonically non-increasing
   (`resourceStep?_energy_nonincreasing`). A contract can spend gas but never mint it.

The input registers are multisets, so one transition consumes exactly one command atom. The aliases
`add-atom`/`addAtom` and `remove-atom`/`remAtom` are accepted, but firing one spelling does not silently
delete the other spelling if both are present. `Operational/SemanticsCoverage.lean` checks those four
alias cases directly. `Operational/Properties.lean` proves the general helper facts
`stepAddAtom_input_eq` and `stepRemAtom_input_eq`, plus one dispatch theorem for each spelling, so the
matched command atom is the one removed from the input register.

# Program Equivalence: Barbed Bisimulation

Following {citet mops}[], program equality is barbed bisimulation. Two states are equivalent when they
agree on every observable barb, meaning input, workspace, and output atoms, and every step of one is
matched by a step of the other back into the relation. LeaTTa defines this in
`Operational/Bisimulation.lean` and proves bisimilarity is an equivalence relation: reflexive, symmetric,
and transitive. The knowledge base is not observed, matching MOPS's treatment of state.
