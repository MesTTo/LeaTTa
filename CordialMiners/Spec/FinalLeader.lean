-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.FinalLeader
Layer: Spec
Purpose: Weighted ratification and final-leader safety. A target block is ratified by a threshold-heavy
  set of creators whose blocks approve it; final leaders are the anchors the ordering extends from. The
  evidence stack rests on the same weighted-overlap safety as threshold finality, so the
  no-conflicting-ratifications theorem (FL-07) is a corollary of CERT-06.
Imports: CordialMiners.Spec.ThresholdFinality, CordialMiners.Spec.Equivocation
Trusted boundary: human-reviewed spec
Main exports: BlockApproves, ValidRatCert, fl_block_approval_no_conflict,
  fl_07_no_conflicting_ratifications
Open obligations: FL-05 certificate persistence under blocklace extension (the approval relation is
  non-monotone; needs the snapshot-query discipline) is future work.
-/
import CordialMiners.Spec.ThresholdFinality
import CordialMiners.Spec.Equivocation

namespace CordialMiners

variable {P Wave Slot Hash : Type*}

/-- A creator `p` ratifies a target block when it has a block in the blocklace that approves the
    target. Ratification weight is the weight of these ratifying creators. -/
def BlockApproves (L : Blocklace P Wave Slot Hash) (p : P) (target : Block P Wave Slot Hash) : Prop :=
  ∃ blk ∈ L, blk.creator = p ∧ ApprovesBlock L blk target

/-- A ratification certificate is a weighted threshold certificate whose value is the target block and
    whose signers are the ratifying creators. It is valid when the ratifiers are threshold-heavy and
    each one's block approves the target. -/
def ValidRatCert (S : CommitteeSnapshot P) (L : Blocklace P Wave Slot Hash)
    (rc : ThresholdCert P (Block P Wave Slot Hash)) : Prop :=
  ValidCert S (BlockApproves L) rc

/-- A single block cannot approve two conflicting blocks: approving one means not observing any
    conflict with it, but approving the other means observing it. This is the structural reason a
    non-equivocating creator ratifies at most one of two conflicting targets. -/
theorem fl_block_approval_no_conflict {L : Blocklace P Wave Slot Hash}
    {a b b' : Block P Wave Slot Hash} (h : ApprovesBlock L a b) (hb' : b' ∈ L)
    (happ' : ApprovesBlock L a b') : ¬ ConflictBlock b b' :=
  fun hconf => bl_05_approval_excludes_conflict h hb' hconf (bl_05_approval_observes happ')

/-- FL-07 (no conflicting ratifications): under the Byzantine-weight bound and honest ratification
    consistency, two valid ratification certificates cannot ratify conflicting target blocks. A direct
    corollary of CERT-06: ratification is weighted threshold approval, so the weighted-overlap safety
    applies unchanged. -/
theorem fl_07_no_conflicting_ratifications [DecidableEq P]
    (S : CommitteeSnapshot P) (hWF : S.WF) (L : Blocklace P Wave Slot Hash) (honest : Finset P)
    (hNoEquiv : ∀ p ∈ honest, ∀ b b' : Block P Wave Slot Hash,
      BlockApproves L p b → BlockApproves L p b' → b = b')
    (hByz : S.ByzBound honest)
    {rc rc' : ThresholdCert P (Block P Wave Slot Hash)}
    (hrc : ValidRatCert S L rc) (hrc' : ValidRatCert S L rc')
    (hconf : ConflictBlock rc.value rc'.value) : False :=
  cert_06_no_conflicting_threshold_finals S hWF (BlockApproves L) honest hNoEquiv hByz hrc hrc'
    (fun e => hconf.2.2 (congrArg Block.blockHash e))

end CordialMiners
