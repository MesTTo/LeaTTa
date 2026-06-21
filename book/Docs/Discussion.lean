/-
LeaTTa: Chapter: Discussion, limitations, and related work.
-/
import VersoManual
import Illuminate
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Discussion and Limitations" =>
%%%
tag := "sec-discussion"
%%%

This chapter tells you what LeaTTa establishes, what it does not yet establish, and how it relates to prior work.

# What Is Established

LeaTTa gives you an executable minimal-MeTTa kernel and standard library that pass Hyperon's test
corpus at 270 of 270 assertions, together with a metatheory layer in which every theorem is checked by
Lean's kernel with no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`. `#print axioms`
reports only the three standard classical axioms of Mathlib. The kernel metatheory proves
determinism, confluence of the deterministic fragment, soundness and completeness of first-argument
indexing, gradual-type soundness, non-transitivity of consistency for both the relation and the
executable matcher, and a bisimulation tying the indexed kernel to the published operational semantics
at the level of rule firing.

The 1.0 release also establishes two larger extensions around that kernel. The MeTTaIL development
formalizes presentation algebra, the elaboration and transform pipeline, the generic reducer, the
monomorphized runtime path, the small external dialect-file parser, and the associated soundness,
sort-preservation, confluence, OSLF, and distributive-law results. The Cordial Miners development
formalizes a PoR-weighted leaderless DAG consensus model and proves end-to-end safety from the named
Byzantine-weight, honest non-equivocation, and finality-permanence assumptions.

# Current Limitations

Here are four boundaries, each stated plainly, each a candidate for the next increment of work.

 * *The kernel matcher's equality oracle.* Because MeTTa atoms embed IEEE floating-point grounded
   values, structural equality on atoms cannot be a lawful `BEq` ({ref "sec-types"}[the float caveat]
   in the object-language chapter). The development never assumes `LawfulBEq Atom`, but several
   matcher lemmas are phrased around a structural-equality oracle rather than a single canonical
   equality. Refactoring the matcher to a structural-bit equality that is lawful by construction,
   with the float comparison isolated, would simplify those proofs.
 * *The typing judgment to kernel bridge.* The well-typedness judgment used in the preservation
   results is a standalone declarative judgment. A lemma connecting it to the kernel's own
   `get-type` computation would make subject reduction speak directly about the types the running
   interpreter reports.
 * *The full query operation.* As noted in {ref "sec-correspondence"}[the correspondence chapter],
   `KernelStep` is the indexed rule-firing core; rule-variable freshening, ambient-binding merge,
   and cyclic-substitution pruning are abstracted out. A lemma relating `queryOp` to `KernelStep`
   up to the existing α-equivalence setoid would lift the bisimulation from the rule-firing core to
   the complete query operation.
 * *The gas model's outcome classification.* The resource-bounded extension proves that energy is
   never created. It does not yet classify a halted configuration as completed, out of gas, or stuck,
   nor prove that a strictly-positive per-step cost yields termination within a fixed budget. The
   ingredients are present; a three-way outcome type would complete the on-chain metering story.
 * *The MeTTaIL external file format.* The `--mettail` runner is the public entry point for editable
   dialect files, but it intentionally accepts only `sort`, `term`, and base `rewrite` declarations
   over S-expression terms. The full BNFC MeTTaIL surface parser is not part of 1.0.
 * *The remaining MeTTaIL research layer.* Modal hypercube typing for binder calculi, rho-calculus
   full abstraction, full spice and mq reduction theories, and an operational bisimulation from
   MeTTaIL back to the four-register machine remain outside this release.
 * *Cordial Miners liveness and environment assumptions.* The safety theorem is explicit about the
   consensus assumptions it needs. Network fairness, scheduler fairness, and certificate persistence
   under blocklace extension are not hidden in the theorem; they are modeled as hypotheses or scoped
   as future work.

None of these limitations contradicts a stated result. Each marks where a stated result can be strengthened or its scope widened.

# Related Work

The type-system layer follows the gradual-typing tradition of {citet siekTaha}[], adopting their
consistency relation and extending their non-transitivity result to the executable matcher. The
operational layer is a machine-checked rendering of the MeTTa operational semantics of {citet mops}[],
which its authors propose as an independent specification of the language. The motivation for that
specification and for a language of thought built on metagraph rewriting is given by
{citet goertzelMetagraph}[]. The MeTTaIL layer follows the GSLT and OSLF line of work by Stay and
Meredith, plus Beck and Street for the categorical distributive-law backbone. The consensus layer
formalizes the PoR-weighted Cordial Miners blueprint in the same style: executable reference pieces
where possible, explicit hypotheses where the environment matters, and kernel-checked safety
theorems. The development uses Lean 4 {citep lean4}[] and draws on Mathlib {citep mathlib}[] for
order-theoretic and relational infrastructure.

# Conclusion

LeaTTa shows that MeTTa's minimal interpreter, its gradual type system, the published operational
semantics, the MeTTaIL spec-to-runtime path, and the Cordial Miners safety story can be expressed in
one machine-checked development. It also shows that optimisations and runtime entry points can be
given a proof boundary instead of being treated as implementation folklore. The limitations above mark
where the next increments of work can extend that scope.
