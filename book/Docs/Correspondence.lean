/-
LeaTTa: Chapter: Interpreter ⇔ Specification Correspondence.
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

#doc (Manual) "Interpreter ⇔ Specification" =>
%%%
tag := "sec-correspondence"
%%%

LeaTTa contains two semantics for MeTTa: the first-argument-indexed interpreter ({ref "sec-interpreter"}[the kernel]) and the published whole-knowledge-base operational semantics ({ref "sec-operational"}[MOPS]). The 2025 Hyperon whitepaper's "GSLT" calls for a formal proof that these two agree. This chapter delivers that correspondence at the level of which rules fire and what they produce.

# QUERY Reduces to the Same Set

`kernel_query_eq_mops_query` proves that, for a head-keyed query, the kernel's *indexed* candidate firing produces exactly the MOPS whole-space `QUERY` reduct set. The optimisation drops no reduct and invents none. The proof follows from the indexing soundness and completeness results in {ref "sec-meta"}[the metatheory] (`candidates_sound`, `candidates_complete`): the head bucket contains precisely the rules that could match, so scanning it loses nothing.

# A Bisimulation

Start at a single step, then lift to the whole reduction relation:

 * The kernel's one-step rewriting (`KernelStep`) and the MOPS one-step rewriting (`MopsStep`) coincide (`kernelStep_iff_mopsStep`).
 * The identity on atoms is therefore a bisimulation between them (`kernel_mops_bisim`).
 * Their reflexive-transitive closures agree (`reflTransGen_kernelStep_iff_mops`).

The two semantics agree over entire evaluation sequences, not only per step.

```diagram (cssWidth := "24em")
cd do
  let a ← CDM.node "t" cdBlue
  let a' ← CDM.node "t'" cdBlue
  let b ← CDM.node "t" cdGreen
  let b' ← CDM.node "t'" cdGreen
  CDM.grid #[#[some a, some a'], #[some b, some b']]
  CDM.arrow a a' (some "KernelStep") cdBlue .above
  CDM.arrow b b' (some "MopsStep") cdGreen .below
  CDM.arrow a b (some "=") cdInk .left
  CDM.arrow a' b' (some "=") cdInk .right
```

# Honest Scope

`KernelStep` is the kernel's indexed *rule-firing core*: the `candidates` matched against the redex. It corresponds to MOPS at the reduct-set level. It is *not yet* the full `queryOp`. Three things are abstracted out:

 * rule-variable freshening;
 * ambient-binding merge;
 * cyclic-substitution pruning.

Rules added to the space at runtime (`world.selfExtra`, consulted by `candidatesW`) are also out of scope. The correspondence is stated over the static knowledge base. A lemma connecting `queryOp` to `KernelStep` up to α-equivalence (the α-equivalence setoid already exists in the development) is recorded as future work in the discussion chapter. What is proved here is that first-argument indexing leaves the reduct set unchanged: which rules fire and what they produce.
