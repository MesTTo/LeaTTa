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

A verification effort is only as valuable as it is honest about its boundary. This chapter states
what LeaTTa establishes, what it does not yet establish, and how the present development relates to
prior work.

# What Is Established

LeaTTa provides an executable minimal-MeTTa kernel and standard library that pass Hyperon's own test
corpus at 270 of 270 assertions, together with a metatheory layer in which every theorem is checked
by Lean's kernel with no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`, and in which
`#print axioms` reports only the three standard classical axioms of Mathlib. Within that layer the
development proves determinism, confluence of the deterministic fragment, soundness and completeness
of first-argument indexing, gradual-type soundness, the non-transitivity of consistency for both the
relation and the executable matcher, and a bisimulation tying the indexed kernel to the published
operational semantics at the level of rule firing.

# Current Limitations

Four boundaries are worth stating plainly, each a candidate for the next increment of work.

 * *The kernel matcher's equality oracle.* Because MeTTa atoms embed IEEE floating-point grounded
   values, structural equality on atoms cannot be a lawful `BEq` ({ref "sec-types"}[the float caveat]
   in the object-language chapter). The development is careful never to assume `LawfulBEq Atom`, but
   several matcher lemmas are therefore phrased around a structural-equality oracle rather than a
   single canonical equality. Refactoring the matcher to a structural-bit equality that is lawful by
   construction, with the float comparison isolated, would simplify those proofs and is the cleanest
   next step.
 * *The typing judgment to kernel bridge.* The well-typedness judgment used in the preservation
   results is a standalone declarative judgment. A lemma connecting it to the kernel's own
   `get-type` computation would close the gap between the declarative type system and the executable
   type checker, so that subject reduction speaks directly about the types the running interpreter
   reports.
 * *The full query operation.* As stated in {ref "sec-correspondence"}[the correspondence chapter],
   `KernelStep` is the indexed rule-firing core, and rule-variable freshening, ambient-binding merge,
   and cyclic-substitution pruning are abstracted out of it. A lemma relating the full `queryOp` to
   `KernelStep` up to the existing α-equivalence setoid would lift the bisimulation from the
   rule-firing core to the complete query operation.
 * *The gas model's outcome classification.* The resource-bounded extension proves that energy is
   never created. It does not yet classify a halted configuration as completed, out of gas, or stuck,
   nor prove that a strictly-positive per-step cost yields termination within a fixed budget. The
   ingredients are present, and a clean three-way outcome type would complete the on-chain metering
   story.

None of these limitations undermines a result that is stated; each marks where a stated result can be
strengthened or its scope widened.

# Related Work

LeaTTa's type-system layer sits in the gradual-typing tradition begun by {citet siekTaha}[], whose
consistency relation it adopts and whose non-transitivity it both reproves and extends to the
executable matcher. Its operational layer is a machine-checked rendering of the MeTTa operational
semantics of {citet mops}[], whose authors propose that semantics as an independent specification of
the language. The motivation for that specification, and for a language of thought built on
metagraph rewriting, is laid out by {citet goertzelMetagraph}[]. The development is carried out in
Lean 4 {citep lean4}[] and draws on Mathlib {citep mathlib}[] for its order-theoretic and
relational infrastructure.

# Conclusion

The case LeaTTa makes is narrow but, within its scope, complete: that MeTTa's minimal interpreter,
its gradual type system, and the published operational semantics can be expressed in one machine-
checked development, and that the optimisations a production evaluator relies on can be proved
faithful to the specification the network agrees on. For a language headed toward on-chain use, that
combination of an executable specification and a checked correspondence is the foundation the rest of
the verification effort can be built upon.
