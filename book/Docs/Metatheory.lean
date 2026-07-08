-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/- jscpd:ignore-start -/
/-
LeaTTa: Chapter: The Metatheory.
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

#doc (Manual) "The Metatheory" =>
%%%
tag := "sec-meta"
%%%
/- jscpd:ignore-end -/

The chapter walks through the machine-checked metatheory. Every result here is a theorem in Lean's
kernel. The development contains no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`.
The public axiom audit files report only Mathlib's three standard classical axioms (`propext`,
`Classical.choice`, `Quot.sound`) where those library paths require them. The gradual-typing
non-transitivity result depends on no axioms at all.

The audit files are explicit: `MettaHyperonFull/Distributed/AxiomAudit.lean`,
`MeTTaILProofs/AxiomAudit.lean`, `CordialMiners/AxiomAudit.lean`, and
`CordialMiners/Runtime/AxiomAudit.lean`. The root CI build also fails on any Lean or Lake warning.
A proof that starts leaning on a placeholder warning cannot slip through as a green build. The book CI
separately builds the Verso source and generated site. Book CI fails on every book warning except the
reviewed upstream Verso v4.31.0 `@[expose]` warning.

# Determinism and Replayability

The abstract machine `interpretStack1` / `mettaEval` is a Lean *total function*: give it equal inputs and
it returns equal outputs. The theorems are `interpretStack1_deterministic` and
`mettaEval_deterministic`.

All of MeTTa's apparent non-determinism lives in the returned result `List`, never in the transition
relation itself. The branching factor of a step is exactly the product of the per-argument result counts,
proved by `cartesian_length`. For a contract language this is the replayability property: re-running on
the same state always returns the same result list.

# Confluence of the Deterministic Fragment

MeTTa's reduction is non-confluent by design. `(superpose (1 2))` reduces to both `1` and `2`, which are
distinct normal forms, so global confluence is false. What is proved is that the deterministic fragment,
configurations with a single successor, is confluent (Church-Rosser):

 * `deterministic_confluent` is the general theorem that a functional one-step relation is confluent
   over its reflexive-transitive closure.
 * `detStep_confluent` applies it to the single-successor sub-relation of the machine.

```diagram (cssWidth := "16em")
cd do
  let a ← CDM.node "a" cdInk
  let b ← CDM.node "b" cdInk
  let c ← CDM.node "c" cdInk
  let d ← CDM.node "d" cdInk
  CDM.grid #[#[some a, some b], #[some c, some d]]
  CDM.arrow a b (some "∗") cdBlue .above
  CDM.arrow a c (some "∗") cdBlue .left
  CDM.arrow b d (some "∗") cdBlue .right
  CDM.arrow c d (some "∗") cdBlue .below
```

# Type Soundness

The type-soundness story ({ref "sec-types"}[the type-system chapter]) has two halves. Both are proved
against the real kernel functions:

 * _Progress / permissiveness_: the gradual checker never rejects a well-typed program spuriously.
   `getTypes` is total (`getTypes_ne_nil`), and the `%Undefined%`/`Atom` wildcards always match.
 * _Preservation_: for the grounded core, arithmetic stays in `Number` and comparison/`==` yields `Bool`
   or propagates an error. For user-defined `=`-rewriting, `reduction_preserves_type` establishes
   subject reduction: a type-preserving rule, applied under any grounding substitution, preserves the
   type. The proof rests on the substitution lemma `WT.subst`. Scope note: `WT` is a standalone
   declarative judgment. A bridge to the kernel's own `getTypes` computation is left as future work.

# First-Argument Indexing: Sound *and* Complete

The interpreter does not scan the whole knowledge base on every reduction. The interpreter indexes
equality rules by the head symbol of their left-hand side and consults only the matching bucket. The
optimisation is proved both sound and complete:

 * `candidates_sound`: every candidate is a genuine rule.
 * `candidates_complete`: every rule that could fire is offered.

Both proofs rest on `matchAtoms_headKey`: matching forces head agreement, so a rule sitting in a
different bucket can never match. Indexing drops no firing rule and invents none.

# Gradual Consistency

The consistency relation `~` of {ref "sec-types"}[the type system] is proved reflexive and symmetric but
not transitive (`Consistent.not_transitive`). The executable `matchType` inherits the same
non-transitivity (`matchType_not_transitive`). The property holds of the code that runs, not merely of a
separate declarative relation.

# α-Equivalence and Substitution

The infrastructure results are:

 * α-equivalence is an equivalence relation, packaged as a `Setoid`, that coincides with equality on
   variable-free atoms. See the IEEE float caveat in {ref "sec-atoms"}[the object-language chapter].
 * `Subst.apply_compose` establishes the substitution composition law on which the reduction-preservation
   proofs depend.
 * `SubstitutionAudit.lean` records the cycle boundary: one-pass substitution does not chase a
   two-variable cycle recursively, and fuel-bounded recursive resolution is not stable on cyclic
   bindings without a separate acyclicity condition.

# Binding, Atomspace, and Observation Laws

The executable binding and atomspace code now has theorem names for the facts later layers use.
`BindingLaws.lean` exposes fresh direct binding, same-value replay, conflict, and
unification-mediated merge cases for `Bindings.addVarBinding` and `Bindings.merge`. The conflict
theorem names the important boundary: inequality alone is not enough, because distinct values can
still merge when `Unify.unifyTop` succeeds.

`SpaceLaws.lean` and `WorldLaws.lean` cover the list-backed atomspace and threaded world operations.
The checked facts include insert visibility through `contains`, query visibility through
`Space.query_insert_self`, exact single-copy removal through `Space.removeOne_insert_self`,
type-assignment and equality-rule visibility, named-space creation and append, state-store updates,
token binding, `&self` append, hidden-import append, and `&self` erase.

`Minimal/Observation.lean` is the theorem-facing observation bridge. `observeQuery` records the input
query, fuel, result atoms, error atoms, stack-overflow status, and before/after world state produced
by the existing evaluator. The theorems `observeQuery_fuel`, `observeQuery_results`,
`observeQuery_errors`, `observeQuery_exhausted`, `observeQuery_worldBefore`, and
`observeQuery_worldAfter` say each field is exactly the corresponding runtime value.

# Host and Type-Constructor Boundaries

`Core/HostLaws.lean` makes native grounded assumptions explicit. A theorem that relies on an external
carrier should receive `NativeCarrierLaws` or `GroundingLaws`, instead of treating host equality,
matching, typing, execution, or display as an implicit trusted boundary. The file introduces no
carrier inhabitants and no project axioms.

`TypeConstructors.lean` pins the executable arrow helpers to their intended shape. `Atom.mkArrow` is
recognized as an arrow type, `TypeEnv.arrowParts?` recovers exactly the argument and return types from
that constructor, and non-arrow or incomplete arrow forms do not split as arrows.

# Distributed Atomspace

`MettaHyperonFull.Distributed.DAS` is separate from Cordial Miners. It models replica-local atom
storage, add/remove events, vector clocks, local issue, remote delivery, and the boundary between
fairness, replay order, and convergence.

The checked vector-clock facts include reflexivity, transitivity, antisymmetry as component equality,
component reads of pairwise max, max as an upper bound, and max as the least upper bound. The system
facts include read-your-own-writes, mid-flight divergence before remote delivery, monotone global logs,
eventual delivery from an explicit `FairDeliveryFrom` parameter, barrier extension under that
fairness parameter, quiescent per-event coverage, ordered atom-set convergence under
`OrderedReplayAssumptions`, and matching convergence after ordered replay.
