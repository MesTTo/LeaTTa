/-
Module: CordialMiners.Tfine.Abstraction
Layer: Tfine
Purpose: The fine theory T_fine and the abstraction map alpha : T_fine -> T_rec. The fine facts carry
  the operational evidence the coarse theory drops (the signer set behind each approval, certificate,
  and final). alpha forgets that evidence by mapping each fine fact to its coarse shadow. The headline
  is a forward simulation (tfine_refines_trec): every fine step is matched by a coarse step or leaves
  the abstraction unchanged. Reachability transfers along alpha (alpha_reachable), so the coarse safety
  invariant lifts to every reachable fine state (tfine_reachable_wf). This is the refinement that lets
  the proof-friendly coarse theorems govern the evidence-carrying operational layer.
Imports: CordialMiners.Trec.Safety
Trusted boundary: none (fully proved)
Main exports: TfineFact, alphaFact, alpha, TfineState.Step, tfine_refines_trec, alpha_reachable,
  tfine_reachable_wf
Open obligations: none
-/
import CordialMiners.Trec.Safety

namespace CordialMiners

/-- A fine protocol fact: the coarse facts plus the operational evidence. An approval, certificate, and
    final each carry the signer set `S` that the coarse theory abstracts away. -/
inductive TfineFact (P Wave Hash : Type*) where
  | propose (w : Wave) (h : Hash)
  | qApprove (w : Wave) (h : Hash) (signers : Finset P)
  | certThresh (w : Wave) (h : Hash) (signers : Finset P)
  | final (w : Wave) (h : Hash) (signers : Finset P)
  | finalLeader (w : Wave) (h : Hash)
  | orderedPrefix (hs : List Hash)
deriving DecidableEq

/-- The abstraction on facts: forget the signer-set evidence, keep the coarse shape. -/
def alphaFact {P Wave Hash : Type*} : TfineFact P Wave Hash → TrecFact Wave Hash
  | .propose w h => .propose w h
  | .qApprove w h _ => .qApprove w h
  | .certThresh w h _ => .certThresh w h
  | .final w h _ => .final w h
  | .finalLeader w h => .finalLeader w h
  | .orderedPrefix hs => .orderedPrefix hs

/-- A fine state is the finite set of fine facts established so far. -/
abbrev TfineState (P Wave Hash : Type*) := Finset (TfineFact P Wave Hash)

variable {P Wave Hash : Type*} [DecidableEq P] [DecidableEq Wave] [DecidableEq Hash]

/-- The abstraction on states: take the image of every fine fact under `alphaFact`. -/
def alpha (s : TfineState P Wave Hash) : TrecState Wave Hash := s.image alphaFact

omit [DecidableEq P] in
/-- The abstraction of the empty fine state is the empty coarse state. -/
theorem alpha_empty : alpha (∅ : TfineState P Wave Hash) = (∅ : TrecState Wave Hash) := by
  simp [alpha]

/-- The abstraction commutes with insertion: abstracting a state with one more fact is the abstract
    state with that fact's coarse shadow inserted. -/
theorem alpha_insert (f : TfineFact P Wave Hash) (s : TfineState P Wave Hash) :
    alpha (insert f s) = insert (alphaFact f) (alpha s) := by
  simp [alpha, Finset.image_insert]

/-- The fine step relation mirrors the coarse one but threads the signer-set evidence: an approval,
    certificate, or final records the witnessing signers `S`. -/
inductive TfineState.Step : TfineState P Wave Hash → TfineState P Wave Hash → Prop where
  | propose (s : TfineState P Wave Hash) (w : Wave) (h : Hash) :
      TfineState.Step s (insert (TfineFact.propose w h) s)
  | qapprove (s : TfineState P Wave Hash) (w : Wave) (h : Hash) (S : Finset P) :
      TfineFact.propose w h ∈ s → TfineState.Step s (insert (TfineFact.qApprove w h S) s)
  | certify (s : TfineState P Wave Hash) (w : Wave) (h : Hash) (S : Finset P) :
      TfineFact.qApprove w h S ∈ s → TfineState.Step s (insert (TfineFact.certThresh w h S) s)
  | finalize (s : TfineState P Wave Hash) (w : Wave) (h : Hash) (S : Finset P) :
      TfineFact.certThresh w h S ∈ s → TfineState.Step s (insert (TfineFact.final w h S) s)
  | finalLead (s : TfineState P Wave Hash) (w : Wave) (h : Hash) (S : Finset P) :
      TfineFact.final w h S ∈ s → TfineState.Step s (insert (TfineFact.finalLeader w h) s)
  | order (s : TfineState P Wave Hash) (hs : List Hash) :
      TfineState.Step s (insert (TfineFact.orderedPrefix hs) s)

/-- Forward simulation (the refinement): every fine step is matched by a coarse step on the abstracted
    states, or it leaves the abstraction unchanged (when the fact's coarse shadow was already present,
    e.g. a second certificate for the same value with different signers). The coarse precondition is
    always met because the fine precondition's coarse shadow lies in the abstracted state. -/
theorem tfine_refines_trec {s s' : TfineState P Wave Hash} (h : TfineState.Step s s') :
    TrecState.Step (alpha s) (alpha s') ∨ alpha s = alpha s' := by
  cases h with
  | propose w h =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.propose (P := P) w h) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.propose (alpha s) w h)
  | qapprove w h S hpre =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.qApprove w h S) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.qapprove (alpha s) w h (Finset.mem_image_of_mem alphaFact hpre))
  | certify w h S hpre =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.certThresh w h S) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.certify (alpha s) w h (Finset.mem_image_of_mem alphaFact hpre))
  | finalize w h S hpre =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.final w h S) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.finalize (alpha s) w h (Finset.mem_image_of_mem alphaFact hpre))
  | finalLead w h S hpre =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.finalLeader (P := P) w h) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.finalLead (alpha s) w h (Finset.mem_image_of_mem alphaFact hpre))
  | order hs =>
    rw [alpha_insert]
    by_cases hm : alphaFact (TfineFact.orderedPrefix (P := P) hs) ∈ alpha s
    · exact Or.inr (Finset.insert_eq_self.mpr hm).symm
    · exact Or.inl (TrecState.Step.order (alpha s) hs)

/-- Reachability transfers along the abstraction: the abstraction of any fine-reachable state is
    coarse-reachable. Steps that change the abstraction become coarse steps; steps that do not are
    absorbed (the abstract state stays put). -/
theorem alpha_reachable {s : TfineState P Wave Hash}
    (h : Relation.ReflTransGen TfineState.Step (∅ : TfineState P Wave Hash) s) :
    Relation.ReflTransGen TrecState.Step (∅ : TrecState Wave Hash) (alpha s) := by
  induction h with
  | refl => rw [alpha_empty]
  | tail _ hstep ih =>
    rcases tfine_refines_trec hstep with hs | heq
    · exact Relation.ReflTransGen.tail ih hs
    · exact heq ▸ ih

/-- The coarse causal well-formedness lifts to the fine theory: every fine-reachable state abstracts
    to a causally well-formed coarse state. The proof-friendly coarse safety therefore governs the
    evidence-carrying operational theory. -/
theorem tfine_reachable_wf {s : TfineState P Wave Hash}
    (h : Relation.ReflTransGen TfineState.Step (∅ : TfineState P Wave Hash) s) : TrecWF (alpha s) :=
  trec_reachable_wf (alpha_reachable h)

end CordialMiners
