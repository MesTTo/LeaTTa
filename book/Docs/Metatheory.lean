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
kernel. The development contains no `sorry` or `admit`, and `#print axioms` reports only Mathlib's three
standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`). The gradual-typing
non-transitivity result depends on no axioms at all.

The headline axiom checks are collected in `MeTTaILProofs/AxiomAudit.lean`, which is imported by the
proof root and built in CI. The root CI build also fails on any Lean or Lake warning. A proof that starts
leaning on a placeholder warning cannot slip through as a green build. The book CI separately builds the
Verso source and generated site. Book CI fails on every book warning except the reviewed upstream Verso
v4.31.0 `@[expose]` warning.

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
