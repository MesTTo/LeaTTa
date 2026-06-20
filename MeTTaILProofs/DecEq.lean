/-
Module: MeTTaILProofs.DecEq
Layer: Proofs
Purpose: Decidable equality for the MeTTaIL data model. The kernel layer (`MeTTaIL.Syntax`) only
  needs Boolean `BEq`, because the Scala interpreter compares with structural `.equals`. The
  metatheory wants more: `LawfulBEq`, so a `==` test agrees with logical `=`, and `DecidableEq`, so
  proofs may case-split on equality. The file supplies both for every type in the data model. Three
  types nest through `List` and so cannot be `deriving` (`Cat`, `AST`, `Presentation`); for each we
  prove `LawfulBEq` by mutual structural induction, then derive `DecidableEq`. The remaining types
  are derived directly.
Imports: MeTTaIL.Syntax, Mathlib
Trusted boundary: none (fully proved)
Main exports: LawfulBEq and DecidableEq instances for Cat, AST, Presentation, and the rest of the
  data model; the reflexivity and eq_of_beq lemmas Cat.beq_refl, Cat.eq_of_beq, AST.beq_refl,
  AST.eq_of_beq, Presentation.beq_refl, Presentation.eq_of_beq.
Open obligations: none
-/
import MeTTaIL.Syntax
import Mathlib.Tactic

namespace MeTTaIL

/-! ### `DottedPath` (no nesting) -/

deriving instance ReflBEq, LawfulBEq, DecidableEq for DottedPath

/-! ### `Cat` (nests through `prod : List Cat`) -/

mutual
  /-- `Cat.beq` is reflexive. -/
  theorem Cat.beq_refl : ∀ a : Cat, Cat.beq a a = true
    | .idCat n   => by simp [Cat.beq]
    | .listOf a  => by simp [Cat.beq, Cat.beq_refl a]
    | .arrow a b => by simp [Cat.beq, Cat.beq_refl a, Cat.beq_refl b]
    | .prod cs   => by simp [Cat.beq, Cat.beqList_refl cs]
  /-- `Cat.beqList` is reflexive. -/
  theorem Cat.beqList_refl : ∀ cs : List Cat, Cat.beqList cs cs = true
    | []      => by simp [Cat.beqList]
    | c :: cs => by simp [Cat.beqList, Cat.beq_refl c, Cat.beqList_refl cs]
end

mutual
  /-- `Cat.beq a b = true` implies `a = b`. -/
  theorem Cat.eq_of_beq : ∀ {a b : Cat}, Cat.beq a b = true → a = b
    | .idCat a,   .idCat b,   h => by simp [Cat.beq] at h; subst h; rfl
    | .listOf a,  .listOf b,  h => by
        simp only [Cat.beq] at h; exact congrArg Cat.listOf (Cat.eq_of_beq h)
    | .arrow a b, .arrow c d, h => by
        simp only [Cat.beq, Bool.and_eq_true] at h
        exact congr (congrArg Cat.arrow (Cat.eq_of_beq h.1)) (Cat.eq_of_beq h.2)
    | .prod cs,   .prod ds,   h => by
        simp only [Cat.beq] at h; exact congrArg Cat.prod (Cat.beqList_eq h)
    | .idCat _,   .listOf _,  h => by simp [Cat.beq] at h
    | .idCat _,   .arrow _ _, h => by simp [Cat.beq] at h
    | .idCat _,   .prod _,    h => by simp [Cat.beq] at h
    | .listOf _,  .idCat _,   h => by simp [Cat.beq] at h
    | .listOf _,  .arrow _ _, h => by simp [Cat.beq] at h
    | .listOf _,  .prod _,    h => by simp [Cat.beq] at h
    | .arrow _ _, .idCat _,   h => by simp [Cat.beq] at h
    | .arrow _ _, .listOf _,  h => by simp [Cat.beq] at h
    | .arrow _ _, .prod _,    h => by simp [Cat.beq] at h
    | .prod _,    .idCat _,   h => by simp [Cat.beq] at h
    | .prod _,    .listOf _,  h => by simp [Cat.beq] at h
    | .prod _,    .arrow _ _, h => by simp [Cat.beq] at h
  /-- `Cat.beqList cs ds = true` implies `cs = ds`. -/
  theorem Cat.beqList_eq : ∀ {cs ds : List Cat}, Cat.beqList cs ds = true → cs = ds
    | [],      [],      _ => rfl
    | c :: cs, d :: ds, h => by
        simp only [Cat.beqList, Bool.and_eq_true] at h
        exact congr (congrArg (· :: ·) (Cat.eq_of_beq h.1)) (Cat.beqList_eq h.2)
    | [],      _ :: _,  h => by simp [Cat.beqList] at h
    | _ :: _,  [],      h => by simp [Cat.beqList] at h
end

instance : LawfulBEq Cat where
  eq_of_beq := Cat.eq_of_beq
  rfl := Cat.beq_refl _

instance : DecidableEq Cat := fun a b =>
  decidable_of_iff (Cat.beq a b = true)
    ⟨Cat.eq_of_beq, fun h => by subst h; exact Cat.beq_refl _⟩

/-! ### `Label`, `Item`, `Rule` (mention `Cat`, no `List` nesting of themselves) -/

deriving instance ReflBEq, LawfulBEq, DecidableEq for Label
deriving instance ReflBEq, LawfulBEq, DecidableEq for Item
deriving instance ReflBEq, LawfulBEq, DecidableEq for Rule

/-! ### `AST` (nests through `sexp ... : List AST`) -/

mutual
  /-- `AST.beq` is reflexive. -/
  theorem AST.beq_refl : ∀ a : AST, AST.beq a a = true
    | .var p        => by simp [AST.beq]
    | .sexp l cs    => by simp [AST.beq, AST.beqList_refl cs]
    | .subst b r v  => by simp [AST.beq, AST.beq_refl b, AST.beq_refl r]
  /-- `AST.beqList` is reflexive. -/
  theorem AST.beqList_refl : ∀ cs : List AST, AST.beqList cs cs = true
    | []      => by simp [AST.beqList]
    | c :: cs => by simp [AST.beqList, AST.beq_refl c, AST.beqList_refl cs]
end

mutual
  /-- `AST.beq a b = true` implies `a = b`. -/
  theorem AST.eq_of_beq : ∀ {a b : AST}, AST.beq a b = true → a = b
    | .var p,       .var q,        h => by simp [AST.beq] at h; subst h; rfl
    | .sexp l cs,   .sexp m ds,    h => by
        simp only [AST.beq, Bool.and_eq_true] at h
        obtain ⟨hl, hd⟩ := h
        have hl' : l = m := LawfulBEq.eq_of_beq hl
        subst hl'
        exact congrArg (AST.sexp l) (AST.beqList_eq hd)
    | .subst b r v, .subst b' r' v', h => by
        simp only [AST.beq, Bool.and_eq_true] at h
        obtain ⟨⟨hb, hr⟩, hv⟩ := h
        have hb' : b = b' := AST.eq_of_beq hb
        have hr' : r = r' := AST.eq_of_beq hr
        have hv' : v = v' := LawfulBEq.eq_of_beq hv
        subst hb'; subst hr'; subst hv'; rfl
    | .var _,       .sexp _ _,     h => by simp [AST.beq] at h
    | .var _,       .subst _ _ _,  h => by simp [AST.beq] at h
    | .sexp _ _,    .var _,        h => by simp [AST.beq] at h
    | .sexp _ _,    .subst _ _ _,  h => by simp [AST.beq] at h
    | .subst _ _ _, .var _,        h => by simp [AST.beq] at h
    | .subst _ _ _, .sexp _ _,     h => by simp [AST.beq] at h
  /-- `AST.beqList cs ds = true` implies `cs = ds`. -/
  theorem AST.beqList_eq : ∀ {cs ds : List AST}, AST.beqList cs ds = true → cs = ds
    | [],      [],      _ => rfl
    | c :: cs, d :: ds, h => by
        simp only [AST.beqList, Bool.and_eq_true] at h
        exact congr (congrArg (· :: ·) (AST.eq_of_beq h.1)) (AST.beqList_eq h.2)
    | [],      _ :: _,  h => by simp [AST.beqList] at h
    | _ :: _,  [],      h => by simp [AST.beqList] at h
end

instance : LawfulBEq AST where
  eq_of_beq := AST.eq_of_beq
  rfl := AST.beq_refl _

instance : DecidableEq AST := fun a b =>
  decidable_of_iff (AST.beq a b = true)
    ⟨AST.eq_of_beq, fun h => by subst h; exact AST.beq_refl _⟩

/-! ### `Equation`, `Hyp`, `Rewrite`, `RewriteDecl` (mention `AST` / `DottedPath`) -/

deriving instance ReflBEq, LawfulBEq, DecidableEq for Equation
deriving instance ReflBEq, LawfulBEq, DecidableEq for Hyp
deriving instance ReflBEq, LawfulBEq, DecidableEq for Rewrite
deriving instance ReflBEq, LawfulBEq, DecidableEq for RewriteDecl

/-! ### `Presentation` (nests through `references : List (String × Presentation)`) -/

mutual
  /-- `Presentation.beq` is reflexive. -/
  theorem Presentation.beq_refl : ∀ p : Presentation, Presentation.beq p p = true
    | .mk e t q r m => by simp [Presentation.beq, Presentation.beqRefs_refl m]
  /-- `Presentation.beqRefs` is reflexive. -/
  theorem Presentation.beqRefs_refl :
      ∀ m : List (String × Presentation), Presentation.beqRefs m m = true
    | []           => by simp [Presentation.beqRefs]
    | (s, p) :: m  => by
        simp [Presentation.beqRefs, Presentation.beq_refl p, Presentation.beqRefs_refl m]
end

mutual
  /-- `Presentation.beq p q = true` implies `p = q`. -/
  theorem Presentation.eq_of_beq :
      ∀ {p q : Presentation}, Presentation.beq p q = true → p = q
    | .mk e₁ t₁ q₁ r₁ m₁, .mk e₂ t₂ q₂ r₂ m₂, h => by
        simp only [Presentation.beq, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨he, ht⟩, hq⟩, hr⟩, hm⟩ := h
        have he' : e₁ = e₂ := LawfulBEq.eq_of_beq he
        have ht' : t₁ = t₂ := LawfulBEq.eq_of_beq ht
        have hq' : q₁ = q₂ := LawfulBEq.eq_of_beq hq
        have hr' : r₁ = r₂ := LawfulBEq.eq_of_beq hr
        have hm' : m₁ = m₂ := Presentation.beqRefs_eq hm
        subst he'; subst ht'; subst hq'; subst hr'; subst hm'; rfl
  /-- `Presentation.beqRefs m₁ m₂ = true` implies `m₁ = m₂`. -/
  theorem Presentation.beqRefs_eq :
      ∀ {m₁ m₂ : List (String × Presentation)}, Presentation.beqRefs m₁ m₂ = true → m₁ = m₂
    | [],           [],           _ => rfl
    | (s, p) :: m₁, (t, q) :: m₂, h => by
        simp only [Presentation.beqRefs, Bool.and_eq_true] at h
        obtain ⟨⟨hs, hp⟩, hm⟩ := h
        have hs' : s = t := LawfulBEq.eq_of_beq hs
        have hp' : p = q := Presentation.eq_of_beq hp
        have hm' : m₁ = m₂ := Presentation.beqRefs_eq hm
        subst hs'; subst hp'; subst hm'; rfl
    | [],           _ :: _,       h => by simp [Presentation.beqRefs] at h
    | _ :: _,       [],           h => by simp [Presentation.beqRefs] at h
end

instance : LawfulBEq Presentation where
  eq_of_beq := Presentation.eq_of_beq
  rfl := Presentation.beq_refl _

instance : DecidableEq Presentation := fun a b =>
  decidable_of_iff (Presentation.beq a b = true)
    ⟨Presentation.eq_of_beq, fun h => by subst h; exact Presentation.beq_refl _⟩

end MeTTaIL
