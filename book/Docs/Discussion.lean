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

This chapter states what LeaTTa establishes, what it does not yet establish, and how it relates to prior
work.

# What Is Established

LeaTTa gives you an executable minimal-MeTTa kernel and standard library that pass Hyperon's test corpus
at 270 of 270 assertions. It also gives a metatheory layer where every theorem is checked by Lean's
kernel with no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`. `#print axioms` reports only
the three standard classical axioms of Mathlib.

The metatheory proves determinism, confluence of the deterministic fragment, soundness and completeness
of first-argument indexing, gradual-type soundness, non-transitivity of consistency for both the relation
and the executable matcher, and a bisimulation tying the indexed kernel to the published operational
semantics at the level of rule firing.

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

None of these limitations contradicts a stated result. Each marks where a stated result can be
strengthened or its scope widened.

# Related Work

The type-system layer follows the gradual-typing tradition of {citet siekTaha}[], adopting their
consistency relation and extending their non-transitivity result to the executable matcher. The
operational layer is a machine-checked rendering of the MeTTa operational semantics of {citet mops}[],
which its authors propose as an independent specification of the language. The motivation for that
specification and for a language of thought built on metagraph rewriting is given by
{citet goertzelMetagraph}[]. The development uses Lean 4 {citep lean4}[] and draws on Mathlib
{citep mathlib}[] for order-theoretic and relational infrastructure.

# Conclusion

LeaTTa shows that MeTTa's minimal interpreter, its gradual type system, and the published operational
semantics can be expressed in one machine-checked development. It also shows that the optimisations a
production evaluator relies on can be proved faithful to the specification. The limitations above mark
where the next increments of work can extend that scope.
