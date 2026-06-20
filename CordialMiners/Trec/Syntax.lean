/-
Module: CordialMiners.Trec.Syntax
Layer: Trec
Purpose: The coarse rewrite theory T_rec: the proof-friendly conceptual facts and steps of the
  protocol (propose, quorum-approve, threshold certificate, final, final leader, ordered prefix),
  with no low-level evidence. The abstraction map alpha : T_fine -> T_rec lands here. The coarse state
  is a finite set of facts that only grows; we prove that growth is monotone.
Imports: CordialMiners.Foundation.Basic
Trusted boundary: human-reviewed spec
Main exports: TrecFact, TrecState, TrecState.Step, trec_step_monotone
Open obligations: the coarse safety theorems (Trec.Safety) and the liveness interface
  (Trec.LivenessInterface) build on this; the fine theory and alpha are the Tfine layer.
-/
import CordialMiners.Foundation.Basic

namespace CordialMiners

/-- A coarse protocol fact (the language of `T_rec`). Evidence-free: a `certThresh` fact records that
    a threshold certificate exists, not the signers or signatures. -/
inductive TrecFact (Wave Hash : Type*) where
  | propose (w : Wave) (h : Hash)
  | qApprove (w : Wave) (h : Hash)
  | certThresh (w : Wave) (h : Hash)
  | final (w : Wave) (h : Hash)
  | finalLeader (w : Wave) (h : Hash)
  | orderedPrefix (hs : List Hash)
deriving DecidableEq

variable {Wave Hash : Type*} [DecidableEq Wave] [DecidableEq Hash]

/-- A coarse state is the finite set of facts established so far. -/
abbrev TrecState (Wave Hash : Type*) := Finset (TrecFact Wave Hash)

/-- The coarse step relation: each conceptual transition adds the fact justified by the facts already
    present. Proposal is always available; the others gate on their precondition fact. The state only
    grows, which is what makes the coarse theory monotone and proof-friendly. -/
inductive TrecState.Step : TrecState Wave Hash → TrecState Wave Hash → Prop where
  | propose (s : TrecState Wave Hash) (w : Wave) (h : Hash) :
      TrecState.Step s (insert (TrecFact.propose w h) s)
  | qapprove (s : TrecState Wave Hash) (w : Wave) (h : Hash) :
      TrecFact.propose w h ∈ s → TrecState.Step s (insert (TrecFact.qApprove w h) s)
  | certify (s : TrecState Wave Hash) (w : Wave) (h : Hash) :
      TrecFact.qApprove w h ∈ s → TrecState.Step s (insert (TrecFact.certThresh w h) s)
  | finalize (s : TrecState Wave Hash) (w : Wave) (h : Hash) :
      TrecFact.certThresh w h ∈ s → TrecState.Step s (insert (TrecFact.final w h) s)
  | finalLead (s : TrecState Wave Hash) (w : Wave) (h : Hash) :
      TrecFact.final w h ∈ s → TrecState.Step s (insert (TrecFact.finalLeader w h) s)
  | order (s : TrecState Wave Hash) (hs : List Hash) :
      TrecState.Step s (insert (TrecFact.orderedPrefix hs) s)

/-- The coarse state only grows: every step adds facts and removes none. -/
theorem trec_step_monotone {s s' : TrecState Wave Hash} (h : TrecState.Step s s') : s ⊆ s' := by
  cases h <;> exact Finset.subset_insert _ _

end CordialMiners
