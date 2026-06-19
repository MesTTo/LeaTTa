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

This chapter surveys the machine-checked metatheory. Each result is a theorem in Lean's kernel; the
development as a whole contains no `sorry` or `admit`, and `#print axioms` reports only Mathlib's
three standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`). The gradual-typing
non-transitivity result depends on no axioms at all.

# Determinism and Replayability

The abstract machine `interpretStack1` / `mettaEval` is a Lean *total function*: applied to equal
inputs it returns equal outputs (`interpretStack1_deterministic`, `mettaEval_deterministic`). All of
MeTTa's non-determinism is reified in the returned result `List`, never in the transition relation;
the branching factor of a step is exactly the product of the per-argument result counts
(`cartesian_length`). For a contract language this is the *replayability* property: re-running on the
same state returns the same result list.

# Confluence of the Deterministic Fragment

MeTTa's reduction is *intentionally* non-confluent: `(superpose (1 2))` reduces to both `1` and `2`,
which are distinct normal forms, so global confluence is false. What is proved is that the
*deterministic fragment* (configurations with a single successor) is confluent (Church–Rosser):
`deterministic_confluent` is the general theorem that a functional one-step relation is confluent over
its reflexive-transitive closure, and `detStep_confluent` applies it to the single-successor
sub-relation of the machine.

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

The type-soundness story ({ref "sec-types"}[the type-system chapter]) has two halves, both proved
against the real kernel functions:

 * _Progress / permissiveness_: the gradual checker never rejects a well-typed program spuriously,
   `getTypes` is total (`getTypes_ne_nil`), and the `%Undefined%`/`Atom` wildcards always match.
 * _Preservation_: for the grounded core, arithmetic stays in `Number` and comparison/`==` yield
   `Bool` or propagate an error; and for user-defined `=`-rewriting, `reduction_preserves_type`
   establishes *subject reduction*: a type-preserving rule, applied under any grounding substitution,
   preserves the type. The proof rests on the substitution lemma `WT.subst`. Note that `WT` is a
   *standalone declarative* judgment; a bridge to the kernel's own `getTypes` computation is left as
   future work (see the discussion chapter).

# First-Argument Indexing: Sound *and* Complete

The interpreter does not scan the whole knowledge base for every reduction; it indexes equality
rules by the head symbol of their left-hand side and consults only the matching bucket. This
optimisation is proved both *sound* (every candidate is a genuine rule, `candidates_sound`) and
*complete* (every rule that could fire is offered, `candidates_complete`). Both proofs rest on
`matchAtoms_headKey`: matching forces head agreement, so a rule in a different bucket can never
match. Indexing drops no firing rule and invents none.

# Gradual Consistency

The consistency relation `~` of {ref "sec-types"}[the type system] is proved reflexive and symmetric
but *not* transitive (`Consistent.not_transitive`). The *executable* `matchType` inherits the same
non-transitivity (`matchType_not_transitive`): the property holds of the code that runs, not merely
of a separate declarative relation.

# α-Equivalence and Substitution

The infrastructure results are: α-equivalence is an equivalence relation (packaged as a `Setoid`)
that coincides with equality on variable-free atoms (see the IEEE float caveat in
{ref "sec-atoms"}[the object-language chapter]); and `Subst.apply_compose` establishes the
substitution composition law on which the reduction-preservation proofs depend.
