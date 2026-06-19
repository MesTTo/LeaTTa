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

This chapter surveys the machine-checked metatheory, the core of the development. Each result is a theorem
in Lean's kernel; the development as a whole contains no `sorry` or `admit`, and `#print axioms`
reports only Mathlib's three standard classical axioms (`propext`, `Classical.choice`, `Quot.sound`),
with the gradual-typing non-transitivity result depending on no axioms at all.

# Determinism and Replayability

The abstract machine `interpretStack1` / `mettaEval` is a Lean *total function*: applied to equal
inputs it returns equal outputs (`interpretStack1_deterministic`, `mettaEval_deterministic`). All of
MeTTa's non-determinism is reified in the returned result `List`, never in the transition relation;
the branching factor of a step is exactly the product of the per-argument result counts
(`cartesian_length`). For a language headed on-chain this is the *replayability* guarantee: re-running
a contract on the same state yields the same result list, deterministically.

# Confluence of the Deterministic Fragment

MeTTa's reduction is *intentionally* non-confluent: `(superpose (1 2))` reduces to both `1` and `2`,
which are distinct normal forms, so LeaTTa is honest that global confluence is therefore false. What is true,
and proved, is that the *deterministic fragment* (configurations with a single successor) is confluent
(Church–Rosser): `deterministic_confluent` is the general theorem that a functional one-step relation
is confluent over its reflexive-transitive closure, and `detStep_confluent` applies it to the
single-successor sub-relation of the machine.

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
   preserves the type. The engine is the substitution lemma `WT.subst`, the standard core of every
   subject-reduction proof. (LeaTTa is candid that `WT` is a *standalone declarative* judgment; a
   proven bridge to the kernel's operational `getTypes` is identified as future work in
   the discussion chapter.)

# First-Argument Indexing: Sound *and* Complete

The interpreter does not scan the whole knowledge base for every reduction; it indexes equality
rules by the head symbol of their left-hand side and consults only the matching bucket. LeaTTa proves
this optimisation is both *sound* (every candidate is a genuine rule, `candidates_sound`) and
*complete* (every rule that could fire is offered, `candidates_complete`). Both rest on the semantic
heart `matchAtoms_headKey`: matching forces head agreement, so a rule in a different bucket can never
match. Indexing therefore drops no firing rule and invents none.

# Gradual Consistency

The consistency relation `~` of {ref "sec-types"}[the type system] is proved reflexive and symmetric
but *not* transitive (`Consistent.not_transitive`), and, notably, the *executable* `matchType`
inherits the same non-transitivity (`matchType_not_transitive`): the property holds of the code that
runs, not merely of an idealized relation beside it.

# α-Equivalence and Substitution

Underpinning the above are the infrastructure results: α-equivalence is an equivalence relation
(packaged as a `Setoid`) that coincides with equality on variable-free atoms (with the honest IEEE
caveat of {ref "sec-atoms"}[the object-language chapter]); and the substitution composition law
`Subst.apply_compose`, the algebraic basis of every reduction-preservation argument.
