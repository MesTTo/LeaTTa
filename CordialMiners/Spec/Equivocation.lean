-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Spec.Equivocation
Layer: Spec
Purpose: Block approval and equivocation evidence. Approval is observation without an observed
  conflict; equivocation evidence is two conflicting blocks by one creator. Proves approval implies
  observation and excludes observed conflicts (BL-05), and that constructed equivocation evidence is
  valid (BL-06).
Imports: CordialMiners.Spec.Blocklace
Trusted boundary: human-reviewed spec
Main exports: ApprovesBlock, bl_05_approval_observes, bl_05_approval_excludes_conflict,
  EquivEvidence, ValidEquivEvidence, mkEquivEvidence, bl_06_equiv_sound
Open obligations: BL-07 exclusion monotonicity (a state-level property) is future work.
-/
import CordialMiners.Spec.Blocklace

namespace CordialMiners

variable {P Wave Slot Hash : Type*}

/-- Block approval: `a` observes `b` and does not observe any block conflicting with `b`. Observing a
    block is not enough to approve it if the observer also observes an equivocation against it. -/
def ApprovesBlock (L : Blocklace P Wave Slot Hash) (a b : Block P Wave Slot Hash) : Prop :=
  Observes L a b ∧ ¬ ∃ c, c ∈ L ∧ Observes L a c ∧ ConflictBlock b c

/-- BL-05: approval implies observation. -/
theorem bl_05_approval_observes {L : Blocklace P Wave Slot Hash} {a b : Block P Wave Slot Hash}
    (h : ApprovesBlock L a b) : Observes L a b := h.1

/-- BL-05: an approver of `b` does not observe any block conflicting with `b`. -/
theorem bl_05_approval_excludes_conflict {L : Blocklace P Wave Slot Hash}
    {a b c : Block P Wave Slot Hash} (h : ApprovesBlock L a b) (hc : c ∈ L)
    (hconf : ConflictBlock b c) : ¬ Observes L a c :=
  fun hobs => h.2 ⟨c, hc, hobs, hconf⟩

/-- Equivocation evidence: two conflicting blocks attributed to one participant. -/
structure EquivEvidence (P Wave Slot Hash : Type*) where
  participant : P
  block1 : Block P Wave Slot Hash
  block2 : Block P Wave Slot Hash

/-- Validity of equivocation evidence relative to a blocklace: both blocks present, both by the named
    participant, and conflicting. -/
def ValidEquivEvidence (L : Blocklace P Wave Slot Hash) (e : EquivEvidence P Wave Slot Hash) : Prop :=
  e.block1 ∈ L ∧ e.block2 ∈ L ∧
  e.block1.creator = e.participant ∧ e.block2.creator = e.participant ∧
  ConflictBlock e.block1 e.block2

/-- Construct equivocation evidence from two conflicting blocks (canonical participant = creator). -/
def mkEquivEvidence (b c : Block P Wave Slot Hash) : EquivEvidence P Wave Slot Hash :=
  ⟨b.creator, b, c⟩

/-- BL-06 (equivocation evidence soundness): evidence built from two in-blocklace conflicting blocks
    by the same creator is valid. -/
theorem bl_06_equiv_sound {L : Blocklace P Wave Slot Hash} {b c : Block P Wave Slot Hash}
    (hb : b ∈ L) (hc : c ∈ L) (hconf : ConflictBlock b c) :
    ValidEquivEvidence L (mkEquivEvidence b c) :=
  ⟨hb, hc, rfl, hconf.1.symm, hconf⟩

end CordialMiners
