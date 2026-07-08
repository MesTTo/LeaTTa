-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Correspondence
Layer: Proofs
Purpose: Interpreter-to-specification correspondence for the QUERY step. Shows the kernel's
  first-argument indexed rule firing produces exactly the whole-space QUERY reduct set of the
  published MOPS semantics (arXiv 2305.17218, section 3.3), so indexing drops no reduct and
  fabricates none. The single-step result is lifted to the whole reduction relation, where the
  kernel's and MOPS's steps coincide and the identity witnesses a bisimulation. The proof reuses
  indexing soundness and completeness.
Imports: MettaHyperonFull.Proofs.IndexingComplete, MettaHyperonFull.Operational.Properties,
  Mathlib.Logic.Relation
Trusted boundary: none (fully proved)
Main exports: equalityReductions_eq_firedReducts, kernel_query_eq_mops_query,
  kernel_irreducible_iff_mops_insensitive, MopsStep, KernelStep, kernelStep_iff_mopsStep, IsBisim,
  kernel_mops_bisim, reflTransGen_kernelStep_iff_mops
Open obligations: none. The correspondence covers the reduct-set core on the symbol-headed fragment;
  rule-variable freshening, ambient-binding merge, and loop-pruning are abstracted out of KernelStep
  by design, and runtime additions to &self are outside its scope, as the scope note records.
-/
import MettaHyperonFull.Proofs.IndexingComplete
import MettaHyperonFull.Operational.Properties
import Mathlib.Logic.Relation

/-!
# Interpreter ↔ specification correspondence for the QUERY step

Two MeTTa semantics appear in this development:

* the **published operational specification**: MOPS's `QUERY` rule (Meredith-Goertzel-Warrell-
  Vandervorst, arXiv 2305.17218, §3.3), formalised by `Operational/Semantics.lean : equalityReductions`,
  which scans the *whole* knowledge base and fires every equation `(= l r)` whose left-hand side
  unifies with the redex (MOPS: `σᵢ = unify(t', tᵢ)`, contractum `{K[u₁σ₁]} ++ … ++ {K[uₙσₙ]}`);
* the **executable kernel**: `Minimal/Interpreter.lean : queryOp`, which consults only the
  first-argument **index** (`MinEnv.candidates`, the head bucket plus the head-less rules).

The main result (`kernel_query_eq_mops_query`): for a head-keyed query, the kernel's indexed
candidate firing produces the same reduct set as MOPS's whole-space `QUERY`. The optimisation drops
no reduct and invents none. Hyperon's Graph-Structured Lambda Theory (2025 Hyperon Whitepaper,
§3.4.1) aims at agreement between a fine-grained evaluator and a declarative semantics; this
establishes it at the level of which rules fire and what they produce. Note: the full `queryOp`
additionally freshens rule variables, merges ambient bindings, and prunes cyclic substitutions.
Those steps are abstracted out of the `KernelStep` relation below. The result covers the reduct-set
core; it is not a claim about the whole evaluator. See the scope note.

The proof reuses indexing soundness and completeness from `Proofs/IndexingComplete.lean`
(`candidates_sound`, `candidates_complete`), which rest on the matcher's head-agreement law
(`Proofs/Indexing.lean : matchAtoms_headKey`). The result is the reduct-level corollary of
indexing correctness, stated against the MOPS spec.

The single-step correspondence is then lifted to the whole reduction relation: the kernel's and
MOPS's one-step relations coincide (`kernelStep_iff_mopsStep`), their reflexive-transitive closures
agree (`reflTransGen_kernelStep_iff_mops`), and the identity witnesses a bisimulation
(`kernel_mops_bisim`). The two semantics match over entire evaluation sequences, not just per step.

Scope. The correspondence covers the reduct set and rewriting relation on the symbol-headed
fragment (`headKey = some _`), where the kernel reduces (`queryOp` refuses bare-variable redexes).
The deterministic register-draining (`smallStep?`) and fuelled stack scheduling (`mettaEval`) are
bookkeeping on top of this shared relation. The kernel also α-renames rule variables
(`freshenRule`), threads ambient bindings, and prunes cyclic substitutions; these do not change
which reducts arise and are addressed in `Proofs/Alpha.lean` and `Proofs/Substitution.lean`. The
correspondence is stated over a static knowledge base: rules added to `&self` at runtime
(`world.selfExtra`, consulted by `candidatesW`) are outside the scope of `KernelStep`. The
barbed bisimulation of the 4-register state machine is in `Operational/Bisimulation.lean`.
-/

namespace Metta
open Metta.Minimal

-- `firedReducts` and its sound-and-complete membership lemma `mem_firedReducts` are shared with the
-- MOPS layer, defined once in `Operational/Properties.lean` and reused here.

/-- MOPS's whole-space `QUERY` reducts are the firing of all of the space's equality rules
(`extractRules`): the operational `equalityReductions` over `⟨atoms⟩` is `firedReducts` over the
extracted rules. -/
theorem equalityReductions_eq_firedReducts (atoms : List Atom) (a : Atom) :
    equalityReductions ⟨atoms⟩ a = firedReducts (extractRules atoms) a := by
  rw [equalityReductions_eq]; rfl

/-- **Interpreter ⇔ specification, for QUERY.** For a head-keyed query `toEval`, the kernel's
first-argument-indexed candidate firing yields *exactly* MOPS's whole-space `QUERY` reduct set: an
atom is produced by the indexed evaluator iff it is produced by the published semantics. First-
argument indexing is therefore faithful to the spec: it loses no reduct (`candidates_complete`) and
fabricates none (`candidates_sound`). -/
theorem kernel_query_eq_mops_query {atoms : List Atom} {gt : GroundingTable} {toEval : Atom}
    {k : String} (hk : headKey toEval = some k) (x : Atom) :
    x ∈ firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates toEval) toEval ↔
      x ∈ equalityReductions ⟨atoms⟩ toEval := by
  rw [equalityReductions_eq_firedReducts, mem_firedReducts, mem_firedReducts]
  constructor
  · -- kernel ⇒ spec: a candidate is a genuine rule of the space (soundness).
    rintro ⟨p, hp, b, hb, hxb⟩
    exact ⟨p, candidates_sound atoms gt toEval p hp, b, hb, hxb⟩
  · -- spec ⇒ kernel: a matching rule is offered by the index (completeness).
    rintro ⟨⟨l, r⟩, hp, b, hb, hxb⟩
    have hm : matchAtoms l toEval ≠ [] := List.ne_nil_of_mem hb
    exact ⟨(l, r), candidates_complete atoms gt toEval k l r hk hp hm, b, hb, hxb⟩

/-- **Irreducibility agrees too.** For a head-keyed query, the kernel finds no candidate reduct
(`queryOp` then returns `NotReducible`) if and only if MOPS finds the term `insensitive`: no
equation fires, so MOPS emits it via `OUTPUT`. Together with `kernel_query_eq_mops_query` this
covers the full QUERY/OUTPUT dichotomy: the two semantics reduce to the same set, and agree on
when there is nothing to reduce. (Combine with `equalityStep_eq_none_iff` to read the right side
as MOPS `insensitive`.) -/
theorem kernel_irreducible_iff_mops_insensitive {atoms : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String} (hk : headKey toEval = some k) :
    firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates toEval) toEval = [] ↔
      equalityReductions ⟨atoms⟩ toEval = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun x => not_congr (kernel_query_eq_mops_query hk x)

/-! ## Multi-step bisimulation of the reduction relations

The QUERY correspondences above are lifted from a single step to the whole reduction *relation*.
Both the MOPS small-step machine (`Operational/Semantics.lean : smallStep?`) and the kernel
(`Minimal/Interpreter.lean : queryOp`) reduce an atom against the knowledge base; the surrounding
register-draining / fuel / stack bookkeeping is deterministic scheduling on top of that shared
relation. We package the shared relation and prove the kernel's and MOPS's versions are
bisimilar, the multi-step form of the interpreter-to-specification correspondence that
Hyperon's GSLT aims at (2025 Hyperon Whitepaper, §3.4.1), on the symbol-headed fragment where the
kernel reduces. -/

/-- MOPS one-step rewriting (the QUERY/CHAIN content): a symbol-headed redex `a` rewrites to any of
its whole-knowledge-base reducts. -/
def MopsStep (atoms : List Atom) (a a' : Atom) : Prop :=
  (∃ k, headKey a = some k) ∧ a' ∈ equalityReductions ⟨atoms⟩ a

/-- The kernel's one-step rewriting (the `queryOp` content): a symbol-headed redex `a` rewrites to
any reduct fired from its first-argument-indexed `candidates`. -/
def KernelStep (atoms : List Atom) (gt : GroundingTable) (a a' : Atom) : Prop :=
  (∃ k, headKey a = some k) ∧ a' ∈ firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates a) a

/-- The kernel's and MOPS's one-step relations **coincide**: same redex, same reduct set
(the head-keyed guard makes the empty-key case vacuous on both sides). -/
theorem kernelStep_iff_mopsStep {atoms : List Atom} {gt : GroundingTable} {a a' : Atom} :
    KernelStep atoms gt a a' ↔ MopsStep atoms a a' := by
  unfold KernelStep MopsStep
  refine and_congr_right fun hguard => ?_
  obtain ⟨k, hk⟩ := hguard
  exact kernel_query_eq_mops_query hk a'

/-- A relation `B` is a **bisimulation** between transition relations `s₁` and `s₂`: related states
make matching transitions back into `B`, in both directions. -/
def IsBisim (s₁ s₂ B : Atom → Atom → Prop) : Prop :=
  ∀ a b, B a b →
    (∀ a', s₁ a a' → ∃ b', s₂ b b' ∧ B a' b') ∧
    (∀ b', s₂ b b' → ∃ a', s₁ a a' ∧ B a' b')

/-- **Indexed-reduction ⇔ specification bisimulation.** `KernelStep` (the kernel's indexed
rule-firing core) and the published MOPS whole-space reduction are bisimilar, witnessed by the
identity on atoms: every step of one is matched by an equal step of the other
(`kernelStep_iff_mopsStep`). First-argument indexing is spec-faithful at the reduct-set level.
Note: rule-variable freshening, ambient-binding merge, and loop-pruning are abstracted out of
`KernelStep`; see the scope note. -/
theorem kernel_mops_bisim (atoms : List Atom) (gt : GroundingTable) :
    IsBisim (KernelStep atoms gt) (MopsStep atoms) (· = ·) := by
  rintro a b rfl
  exact ⟨fun a' h => ⟨a', kernelStep_iff_mopsStep.mp h, rfl⟩,
         fun b' h => ⟨b', kernelStep_iff_mopsStep.mpr h, rfl⟩⟩

/-- **Multi-step agreement.** Because the one-step relations coincide, so do their reflexive-
transitive closures: an atom reaches `b` by any number of kernel reduction steps iff it does by MOPS
reduction steps. The two semantics agree over entire evaluation sequences. -/
theorem reflTransGen_kernelStep_iff_mops (atoms : List Atom) (gt : GroundingTable) (a b : Atom) :
    Relation.ReflTransGen (KernelStep atoms gt) a b ↔ Relation.ReflTransGen (MopsStep atoms) a b := by
  have h : KernelStep atoms gt = MopsStep atoms := by
    funext x y; exact propext kernelStep_iff_mopsStep
  rw [h]

end Metta
