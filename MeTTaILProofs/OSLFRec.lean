/-
Module: MeTTaILProofs.OSLFRec
Layer: Proofs
Purpose: The recursive (greatest-fixed-point) modalities of the OSLF spatial-behavioral logic. Stay and
  Meredith write the confinement and liveness formulae of "Logic as a Distributive Law" with a `mu X. P[X]`
  binder that they interpret as the GREATEST fixed point. The interpretation of a formula is a predicate
  on terms (`Pred = AST -> Prop`), which is a complete lattice, so the greatest fixed point of a monotone
  formula operator exists by Knaster-Tarski (Mathlib's `OrderHom.gfp`). `nu` is that modality, with the
  fixpoint equation `nu_unfold` and the coinduction principle `le_nu` (to show a property is below `nu F`,
  show it is `F`-consistent). The canonical instance is `alwaysBox`, the invariance/safety modality
  `nu X. A and box X` ("A holds now and after every reduction, forever"), the gfp shape behind
  confinement: `alwaysBox_le` (it implies `A` now), `alwaysBox_coind` (prove an invariant by exhibiting a
  reduction-closed witness), and `alwaysBox_preserved` (it is kept by the runtime, the coinductive
  analogue of `box_preserved`). This is the greatest-fixed-point layer left open by `Semantics/OSLF`.
Imports: MeTTaIL.Semantics.OSLF (Pred and its modalities), Mathlib.Order.FixedPoints (OrderHom.gfp)
Trusted boundary: none (fully proved)
Main exports: box_mono, nu, nu_unfold, le_nu, alwaysBox, alwaysBox_unfold, alwaysBox_le,
  alwaysBox_coind, alwaysBox_preserved
Open obligations: the full 2-categorical distributive-law derivation remains future work.
-/
import MeTTaIL.Semantics.OSLF
import Mathlib.Order.FixedPoints

namespace MeTTaIL.OSLF

/-- `box p` is monotone in its predicate argument: enlarging the target property enlarges `box`. -/
theorem box_mono (p : Presentation) : Monotone (Pred.box p) := by
  intro A B hAB t hbox t' hstep
  exact hAB t' (hbox t' hstep)

/-- The formula operator `X ↦ A and box X`, whose greatest fixed point is the invariance modality. -/
def alwaysBoxOp (p : Presentation) (A : Pred) : Pred →o Pred where
  toFun X := Pred.conj A (Pred.box p X)
  monotone' _ _ hXY t ht := ⟨ht.1, box_mono p hXY t ht.2⟩

/-- The greatest-fixed-point modality. Stay-Meredith's `mu X. P[X]` is read as the greatest fixed point
    of the (monotone) formula operator `F`, the coinductive reading used for confinement and liveness. -/
def nu (F : Pred →o Pred) : Pred := OrderHom.gfp F

/-- The fixpoint equation: `nu F` unfolds to `F (nu F)`. -/
theorem nu_unfold (F : Pred →o Pred) : nu F = F (nu F) := (OrderHom.map_gfp F).symm

/-- Coinduction: any `F`-consistent property (`X ≤ F X`) is below `nu F`. The proof principle for
    establishing a greatest-fixed-point / safety property. -/
theorem le_nu {F : Pred →o Pred} {A : Pred} (h : A ≤ F A) : A ≤ nu F := OrderHom.le_gfp F h

/-- The invariance (always) modality `nu X. A and box X`: `A` holds now and after every reduction step,
    forever. The greatest-fixed-point shape Stay-Meredith use for confinement and other safety
    properties. -/
def alwaysBox (p : Presentation) (A : Pred) : Pred := nu (alwaysBoxOp p A)

/-- `alwaysBox A` unfolds to "`A` now and `box (alwaysBox A)`". -/
theorem alwaysBox_unfold (p : Presentation) (A : Pred) :
    alwaysBox p A = Pred.conj A (Pred.box p (alwaysBox p A)) :=
  nu_unfold (alwaysBoxOp p A)

/-- An invariant holds now. -/
theorem alwaysBox_le (p : Presentation) (A : Pred) {t : AST} (h : alwaysBox p A t) : A t := by
  rw [alwaysBox_unfold] at h; exact h.1

/-- Coinduction for invariance: a property `X` that implies `A` and is preserved by every reduction
    (`X ≤ A and box X`) is below `alwaysBox A`, so every `X`-term is always-`A`. -/
theorem alwaysBox_coind (p : Presentation) (A X : Pred)
    (h : X ≤ Pred.conj A (Pred.box p X)) : X ≤ alwaysBox p A :=
  le_nu h

/-- An invariant is preserved by reduction: the coinductive (greatest-fixed-point) analogue of
    `box_preserved`. A term that is always-`A` stays always-`A` as the runtime reduces it. -/
theorem alwaysBox_preserved (p : Presentation) (A : Pred) {t t' : AST}
    (hstep : RewStepMany p t t') (ht : alwaysBox p A t) : alwaysBox p A t' := by
  rw [alwaysBox_unfold] at ht
  exact ht.2 t' hstep

end MeTTaIL.OSLF
