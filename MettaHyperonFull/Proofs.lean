-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs
Layer: Proofs
Purpose: Aggregator for the metatheory layer. Pulls together every proof module that reasons about
  the executable kernel without taking part in execution. The collected results target what matters
  for on-chain use: determinism, type soundness, confluence of the deterministic fragment, sound and
  complete rule indexing, and interpreter-to-specification correspondence.
Imports: every module under MettaHyperonFull.Proofs (Basic, Substitution, SubstitutionAudit, Alpha,
  Indexing, IndexingComplete, SpaceLaws, WorldLaws, Results, TypeSoundness, Confluence,
  Preservation, Gradual, Correspondence, CorrespondenceR14)
Trusted boundary: none (fully proved)
Main exports: re-exports of the proof modules; no new declarations of its own
Open obligations: none. The 4-register MOPS semantics, its bisimulation, and the gas model live in
  the sibling MettaHyperonFull.Operational library.
-/
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Proofs.Substitution
import MettaHyperonFull.Proofs.SubstitutionAudit
import MettaHyperonFull.Proofs.Alpha
import MettaHyperonFull.Proofs.Indexing
import MettaHyperonFull.Proofs.IndexingComplete
import MettaHyperonFull.Proofs.SpaceLaws
import MettaHyperonFull.Proofs.WorldLaws
import MettaHyperonFull.Proofs.Results
import MettaHyperonFull.Proofs.TypeSoundness
import MettaHyperonFull.Proofs.Confluence
import MettaHyperonFull.Proofs.Preservation
import MettaHyperonFull.Proofs.Gradual
import MettaHyperonFull.Proofs.Correspondence
import MettaHyperonFull.Proofs.CorrespondenceR14

/-!
# Metatheory of the minimal-MeTTa semantics

This library proves properties *about* the executable kernel
(`MettaHyperonFull.Minimal.Interpreter` and the `Core` object language); it does **not**
participate in execution. It may use the full classical / noncomputable Mathlib API
(`Multiset`, `Finset`, `Relation.ReflTransGen`, order theory, `aesop`, …) precisely because
nothing here has to `lake exe`.

MeTTa is headed for use as an on-chain / smart-contract language, so the properties that matter
most are the ones that make execution *predictable and verifiable*: determinism, type soundness,
and that the implementation's optimisations don't change behaviour. Those drive the roadmap.

## Done

* `Proofs/Basic.lean`:         a structural `@[induction_eliminator]` for the nested inductive
                               `Atom`, and renaming/size structural lemmas.
* `Proofs/Substitution.lean`: foundational `Subst.apply` / `instantiate` lemmas: empty-substitution
                               identity, closed atoms are fixed, size monotonicity, and the
                               substitution **composition law** `Subst.apply_compose`.
* `Proofs/SubstitutionAudit.lean`: cyclic substitution audit: one-pass substitution does not chase
                               `$x <- $y <- $x`; repeated resolution is fuel-bounded and can fail
                               fuel-stability without an acyclicity side condition
                               (`cyclicResolve_not_fuel_stable`).
* `Proofs/Alpha.lean`:         α-equivalence is an **equivalence relation**; preserves `Atom.size`;
                               coincides with `=` on variable-free atoms. Documents the Float/IEEE
                               caveat on the Boolean decider.
* `Proofs/Indexing.lean`:      **first-argument rule indexing is sound**: matching forces head
                               agreement (`matchAtoms_headKey`), so the head bucket never hides a
                               firing rule. (Rigorous form of Hyperon improvement #9.)
* `Proofs/IndexingComplete.lean`: first-argument indexing is **sound *and* complete**. The head
                               bucket is *exactly* the head-keyed rules and `varRules` *exactly* the
                               head-less ones (`ruleIndex_getD`, `ofAtomsGT_varRules`); hence every
                               candidate is a genuine rule (`candidates_sound`) and every rule that
                               could match is offered (`candidates_complete`). Indexing drops no
                               firing rule, the very same-head regime in which Hyperon's
                               `Space::visit` *under*-counts (open issue #1079).
* `Proofs/Results.lean`:       **the abstract machine is deterministic**: `interpretStack1`,
                               `interpretFuel`, `mettaEval` are single-valued functions, so all
                               nondeterminism is reified in the result `List`, not in the transition
                               relation (the replayability a blockchain VM needs); plus the
                               `cartesian` branching-factor law.
* `Proofs/TypeSoundness.lean`: the gradual type system is **permissive** (undeclared ops / extra
                               args / `%Undefined%`/`Atom` never rejected), **total** (`getTypes`
                               assigns every atom a type, `getTypes_ne_nil`), unique modulo
                               permutation as a computed type list
                               (`getTypes_unique_modulo_permutation`), reports `BadArgType`
                               **faithfully** (`mettaEval_badArgType`) and only with a **real** actual
                               type (`typeCheckArgs_act_real`: no fabricated errors), and **preserves
                               types on the grounded core**: arithmetic is closed on `Number`
                               (`numBin_isNumber`), comparison/`==` yield `Bool`
                               (`numCmp_isBool`, `eqAtom_isBoolOrError`).
* `Proofs/Confluence.lean`:    the **deterministic fragment is confluent** (Church–Rosser):
                               `interpretStack1`'s single-successor sub-relation is functional
                               (`detStep_functional`), hence confluent (`detStep_confluent`); the
                               branching part is exactly MeTTa's intended nondeterminism, reified in
                               the result list.
* `Proofs/Preservation.lean`: **subject reduction over user-defined `=`-rewriting** (the central
                               type-soundness theorem). A compositional typing judgement `WT`
                               (context for rule variables + `(: a T)` declarations + arrow-elimination
                               application + subtyping/gradual top), defined independently of
                               `Core.HasType` but over the same `(: a T)` declarations; the
                               **substitution lemma** `WT.subst` (typing stable under a
                               context-grounding substitution, the standard core, à la PLFA / PTS /
                               Blanqui); hence `reduction_preserves_type`: for a **type-preserving**
                               rule `(= L R)` (`L`,`R` share a type `T` in the rule's context) and any
                               grounding `σ`, the redex `σL` and contractum `σR` both have type `T`.
                               The type-preserving-rule hypothesis is the formal "the programmer wrote
                               a well-typed rule" (MeTTa never checks `type(L)=type(R)`), and the
                               type is fixed at the rule's `T`, the correct statement for MeTTa's
                               set-valued typing (a rule preserves the type it is written for).
* `Proofs/Gradual.lean`:       **gradual type consistency** as a relation: MeTTa's type compatibility
                               (Hyperon's `match_types`) is Siek–Taha's `~`, **reflexive and symmetric**
                               (`Consistent.refl`, `Consistent.symm`) but pointedly **NOT transitive**
                               (`Consistent.not_transitive`): `Number ~ %Undefined% ~ String` yet
                               `Number ≁ String`. That intransitivity is the whole point: it is what
                               keeps the dynamic type `%Undefined%`/`Atom` sound instead of collapsing
                               every type into one. So compatibility is a *tolerance* relation, not a
                               preorder.

* `Proofs/Correspondence.lean`: **interpreter ⇔ specification for QUERY**: the kernel's first-argument
                               *indexed* rule firing (`MinEnv.candidates`, the rule-firing core
                               abstracted from `queryOp`) produces exactly
                               the **whole-space `QUERY` reduct set of the published MOPS semantics**
                               (`Operational/Semantics.lean : equalityReductions`, MOPS arXiv 2305.17218
                               §3.3), via `kernel_query_eq_mops_query`. Indexing yields the same reduct set
                               (drops no reduct, fabricates none), by reusing `candidates_sound` /
                               `candidates_complete`. This is the GSLT "interpreter ⇔ semantics"
                               correspondence the 2025 Hyperon Whitepaper (§3.4.1) describes, at the QUERY step,
                               the bridge between the efficient on-chain evaluator and the spec.
* `Proofs/CorrespondenceR14.lean`: the same QUERY correspondence packaged as four public obligations:
                               initial agreement, step matching, observation compatibility, and
                               termination preservation (`queryCorrespondenceR14`).
* `Proofs/SpaceLaws.lean` and `Proofs/WorldLaws.lean`: basic list-backed atomspace and threaded-world
                               visibility laws for insert/remove, named spaces, state cells, tokens,
                               `&self`, and imports.

(The published 4-register MOPS operational semantics, its barbed **bisimulation**, and the
resource-bounded **gas** model live in the sibling `MettaHyperonFull.Operational.*` library; see
`Operational/Semantics.lean`, `Operational/Bisimulation.lean`, `Operational/ResourceBounded.lean` and
the properties in `Operational/Properties.lean`.)

The reducible, hand-written `BEq Atom` (`Core/Atom.lean`) is what makes the matcher-level proofs
here possible at all; the derived instance is well-founded and opaque even to `decide`.
-/
