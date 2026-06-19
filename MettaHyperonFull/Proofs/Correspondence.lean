import MettaHyperonFull.Proofs.IndexingComplete
import MettaHyperonFull.Operational.Properties
import Mathlib.Logic.Relation

/-!
# Interpreter ↔ specification correspondence for the QUERY step

This module connects the two MeTTa semantics in this development:

* the **published operational specification**: MOPS's `QUERY` rule (Meredith–Goertzel–Warrell–
  Vandervorst, arXiv 2305.17218, §3.3), formalised by `Operational/Semantics.lean : equalityReductions`,
  which scans the *whole* knowledge base and fires every equation `(= l r)` whose left-hand side
  unifies with the redex (MOPS: `σᵢ = unify(t', tᵢ)`, contractum `{K[u₁σ₁]} ++ … ++ {K[uₙσₙ]}`);
* the **executable kernel**: `Minimal/Interpreter.lean : queryOp`, which does *not* scan the whole
  space: it consults only the first-argument **index** (`MinEnv.candidates`, the head bucket plus the
  head-less rules) for efficiency.

The headline (`kernel_query_eq_mops_query`): for a head-keyed query, the kernel's indexed candidate
firing produces exactly MOPS's whole-space `QUERY` reduct set, so the optimisation drops no reduct
and invents none. This is the interpreter-to-specification correspondence that Hyperon's
Graph-Structured Lambda Theory aims at (2025 Hyperon Whitepaper, §3.4.1), where a fine-grained
evaluator and a declarative semantics are derived from one foundation and kept in agreement, here at
the level of which rules fire and what they produce. The full `queryOp` additionally freshens rule
variables, merges ambient bindings, and prunes cyclic substitutions. Those are abstracted out of the
`KernelStep` relation below, so this result is the reduct-set core of the correspondence rather than a
statement about the whole evaluator. See the scope note.

It is proved by reusing the indexing soundness and completeness already established in
`Proofs/IndexingComplete.lean` (`candidates_sound`, `candidates_complete`), which themselves rest on
the matcher's head-agreement law in `Proofs/Indexing.lean` (`matchAtoms_headKey`). So the present
result is the reduct-level corollary of indexing correctness, stated against the MOPS spec.

This is then lifted below from a single step to the whole reduction relation: the kernel's and MOPS's
one-step rewriting coincide (`kernelStep_iff_mopsStep`), so the identity is a bisimulation between
them (`kernel_mops_bisim`) and their reflexive-transitive closures agree
(`reflTransGen_kernelStep_iff_mops`), so the two semantics match over entire evaluation sequences, not
just per step.

Scope. The correspondence is of the reduct set and rewriting relation, that is, which equations fire
and what each produces, on the symbol-headed fragment (`headKey = some _`), where the kernel reduces
(`queryOp` refuses bare-variable redexes). The deterministic register-draining (`smallStep?`) and
fuelled stack scheduling (`mettaEval`) are bookkeeping on top of this shared relation. The kernel
also α-renames a rule's variables (`freshenRule`), threads ambient bindings, and prunes cyclic
substitutions, none of which change which reducts arise; these are established in `Proofs/Alpha.lean`
and `Proofs/Substitution.lean`. The barbed bisimulation of the 4-register state machine itself is in
`Operational/Bisimulation.lean`.
-/

namespace Metta
open Metta.Minimal

-- `firedReducts` and its sound-and-complete membership lemma `mem_firedReducts` are shared with the
-- MOPS layer, defined once in `Operational/Properties.lean` and reused here.

/-- MOPS's whole-space `QUERY` reducts are exactly the firing of all of the space's equality rules
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
(`queryOp` then returns `NotReducible`) *exactly* when MOPS finds the term `insensitive`: no equation
fires, so MOPS emits it via `OUTPUT`. Together with `kernel_query_eq_mops_query` this is the full
QUERY/OUTPUT dichotomy: the two semantics reduce to the same set, and agree precisely on when there is
nothing to reduce. (Combine with `equalityStep_eq_none_iff` to read the right side as MOPS
`insensitive`.) -/
theorem kernel_irreducible_iff_mops_insensitive {atoms : List Atom} {gt : GroundingTable}
    {toEval : Atom} {k : String} (hk : headKey toEval = some k) :
    firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates toEval) toEval = [] ↔
      equalityReductions ⟨atoms⟩ toEval = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun x => not_congr (kernel_query_eq_mops_query hk x)

/-! ## Multi-step bisimulation of the reduction relations

The two QUERY correspondences above are lifted here from a single step to the whole reduction
*relation*. Both the MOPS small-step machine (`Operational/Semantics.lean : smallStep?`, whose QUERY
and CHAIN cases reduce a redex by `equalityReductions`) and the kernel (`Minimal/Interpreter.lean :
queryOp`, firing the indexed `candidates`) are, at heart, rewriting an atom against the knowledge
base; the surrounding register-draining / fuel / stack bookkeeping is deterministic scheduling on top
of that shared relation. We package the shared relation and prove the kernel's and MOPS's versions
are bisimilar: the multi-step form of the interpreter-to-specification correspondence that Hyperon's
GSLT aims at (2025 Hyperon Whitepaper, §3.4.1), on the symbol-headed fragment where the kernel reduces. -/

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

/-- **Indexed-reduction ⇔ specification bisimulation.** `KernelStep`, the kernel's indexed
rule-firing core that matches `candidates` against the redex, and the published MOPS whole-space
reduction are bisimilar, witnessed by the identity on atoms: every step of one is matched by an equal
step of the other (`kernelStep_iff_mopsStep`). This establishes that first-argument indexing is
spec-faithful at the reduct-set level. It is not a claim about the full `queryOp`: rule-variable
freshening, ambient-binding merge, and loop-pruning are abstracted out of `KernelStep`. See the scope
note. -/
theorem kernel_mops_bisim (atoms : List Atom) (gt : GroundingTable) :
    IsBisim (KernelStep atoms gt) (MopsStep atoms) (· = ·) := by
  rintro a b rfl
  exact ⟨fun a' h => ⟨a', kernelStep_iff_mopsStep.mp h, rfl⟩,
         fun b' h => ⟨b', kernelStep_iff_mopsStep.mpr h, rfl⟩⟩

/-- **Multi-step agreement.** Because the one-step relations coincide, so do their reflexive-
transitive closures: an atom reaches `b` by any number of kernel reduction steps iff it does by MOPS
reduction steps. The two semantics agree not just per step but over entire evaluation sequences. -/
theorem reflTransGen_kernelStep_iff_mops (atoms : List Atom) (gt : GroundingTable) (a b : Atom) :
    Relation.ReflTransGen (KernelStep atoms gt) a b ↔ Relation.ReflTransGen (MopsStep atoms) a b := by
  have h : KernelStep atoms gt = MopsStep atoms := by
    funext x y; exact propext kernelStep_iff_mopsStep
  rw [h]

end Metta
