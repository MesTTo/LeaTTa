/-
Module: MeTTaILProofs.OSLFCat
Layer: Proofs
Purpose: The categorical structure of the OSLF behavioral modalities, the concrete content of Stay and
  Meredith's "Logic as a Distributive Law" (arXiv 1610.02247) at the level of predicates. Because the
  reduction relation `RewStepMany` is reflexive and transitive, the possibility modality `Pred.dia` is a
  closure operator on the predicate preorder (a monad: extensive, monotone, idempotent) and the necessity
  modality `Pred.box` is the dual interior operator (a comonad: deflationary, monotone, idempotent). The
  spatial composition `Pred.spatial` (the distributive law `delta` applied to a binary constructor) is a
  bifunctor on predicates (monotone in each argument). This is the monad/comonad/distributive-law skeleton
  that the 2-categorical account abstracts: the predicate preorder is the thin 2-category and the
  modalities are its (co)monads. The distributive law itself is made concrete: possibility distributes over
  disjunction (`dia_disj`, `dia` preserves joins), necessity over conjunction (`box_conj`, `box` preserves
  meets), and the spatial constructor over disjunction (`spatial_disj_left`, the `delta` lifting a calc
  constructor over the Boolean structure). The abstract backbone is `composeClosure`: in a thin 2-category
  (a partial order) a distributive law of two closure operators yields a composite closure operator, the
  order-theoretic case of Beck's theorem that a distributive law produces a composite monad. The general
  (non-thin) 2-categorical version of that theorem, for arbitrary `CategoryTheory.Monad`s in the 2-category
  `Cat`, is `MeTTaILProofs.DistributiveLaw.composeMonad`; `composeClosure` here is its thin/poset shadow.
Imports: MeTTaIL.Semantics.OSLF (Pred and its modalities), Mathlib.Order.Closure (ClosureOperator),
  Mathlib.Order.FixedPoints (the predicate-preorder instances)
Trusted boundary: none (fully proved)
Main exports: dia_mono, dia_extensive, dia_idem, diaClosure, box_le_self, box_idem, box_interior_eq,
  spatial_mono, composeClosure, dia_disj, box_conj, spatial_disj_left (monotonicity of box is
  `OSLFRec.box_mono`)
-/
import MeTTaIL.Semantics.OSLF
import Mathlib.Order.Closure
import Mathlib.Order.FixedPoints

namespace MeTTaIL.OSLF

open Relation

/-! ### The possibility modality `dia` is a closure operator (a monad)

`Pred.dia` is extensive (`A ≤ dia A`, by reflexivity of reduction), monotone, and idempotent (by
transitivity). Those are exactly the axioms of a closure operator on the predicate preorder. -/

/-- `dia` is monotone: a stronger property has a stronger possibility. -/
theorem dia_mono (p : Presentation) {A B : Pred} (h : A ≤ B) : Pred.dia p A ≤ Pred.dia p B := by
  intro t ht; obtain ⟨t', hr, ha⟩ := ht; exact ⟨t', hr, h t' ha⟩

/-- `dia` is extensive: a term that satisfies `A` already possibly-satisfies `A` (it reduces to itself). -/
theorem dia_extensive (p : Presentation) (A : Pred) : A ≤ Pred.dia p A := by
  intro t ha; exact ⟨t, RewStepMany.refl, ha⟩

/-- `dia` is idempotent: possibly-possibly is possibly (by transitivity of reduction). -/
theorem dia_idem (p : Presentation) (A : Pred) : Pred.dia p (Pred.dia p A) ≤ Pred.dia p A := by
  intro t ht; obtain ⟨t', hr, t'', hr', ha⟩ := ht; exact ⟨t'', hr.trans hr', ha⟩

/-- The behavioral-possibility modality as a closure operator (a monad) on the predicate preorder. -/
def diaClosure (p : Presentation) : ClosureOperator Pred :=
  ClosureOperator.mk' (Pred.dia p) (fun _ _ h => dia_mono p h) (dia_extensive p) (dia_idem p)

/-! ### The necessity modality `box` is an interior operator (a comonad)

Dually, `Pred.box` is deflationary (`box A ≤ A`) and idempotent; monotonicity is `OSLFRec.box_mono`. -/

/-- `box` is deflationary: a term all of whose reducts satisfy `A` satisfies `A` (it reduces to itself). -/
theorem box_le_self (p : Presentation) (A : Pred) : Pred.box p A ≤ A := by
  intro t hb; exact hb t RewStepMany.refl

/-- `box` is idempotent: necessarily is necessarily-necessarily (by transitivity of reduction). -/
theorem box_idem (p : Presentation) (A : Pred) : Pred.box p A ≤ Pred.box p (Pred.box p A) := by
  intro t hb t' hr t'' hr'; exact hb t'' (hr.trans hr')

/-- `box` is an interior operator: `box (box A) = box A`. -/
theorem box_interior_eq (p : Presentation) (A : Pred) : Pred.box p (Pred.box p A) = Pred.box p A :=
  le_antisymm (box_le_self p (Pred.box p A)) (box_idem p A)

/-! ### The spatial distributive law is a bifunctor

`Pred.spatial l` (the distributive law applied to a binary constructor) is monotone in each argument, so
it is functorial on the predicate preorder. -/

/-- The spatial composition is monotone in both arguments. -/
theorem spatial_mono (l : Label) {A A' B B' : Pred} (hA : A ≤ A') (hB : B ≤ B') :
    Pred.spatial l A B ≤ Pred.spatial l A' B' := by
  intro t ht
  cases t with
  | var _ => simp [Pred.spatial] at ht
  | subst _ _ _ => simp [Pred.spatial] at ht
  | sexp m args =>
      cases args with
      | nil => simp [Pred.spatial] at ht
      | cons a as =>
          cases as with
          | nil => simp [Pred.spatial] at ht
          | cons b bs =>
              cases bs with
              | nil =>
                  simp only [Pred.spatial] at ht ⊢
                  obtain ⟨hlm, ha, hb⟩ := ht
                  exact ⟨hlm, hA a ha, hB b hb⟩
              | cons _ _ => simp [Pred.spatial] at ht

/-! ### The abstract distributive law: distributive laws compose monads

In a thin 2-category (a partial order), a monad is a closure operator. A distributive law of one closure
operator over another (`d (c x) ≤ c (d x)`) makes the composite `c ∘ d` a closure operator (a monad), the
order-theoretic case of Beck's theorem that a distributive law yields a composite monad. -/

/-- Beck's distributive law theorem in a thin 2-category: a distributive law of closure operators yields a
    composite closure operator (the composite monad). -/
def composeClosure {α : Type*} [PartialOrder α] (c d : ClosureOperator α)
    (hdl : ∀ x, d (c x) ≤ c (d x)) : ClosureOperator α :=
  ClosureOperator.mk' (fun x => c (d x))
    (fun _ _ h => OrderHomClass.mono c (OrderHomClass.mono d h))
    (fun x => le_trans (d.le_closure' x) (c.le_closure' (d x)))
    (fun x => by
      calc c (d (c (d x))) ≤ c (c (d (d x))) := OrderHomClass.mono c (hdl (d x))
        _ = c (d (d x)) := c.idempotent' _
        _ = c (d x) := congrArg _ (d.idempotent' x))

/-! ### The concrete distributive laws of OSLF (the `delta` content)

The modalities and the spatial constructor distribute over the Boolean connectives: this is the
distributive law `delta` of "logic as a distributive law", made concrete on the term model. Possibility
distributes over disjunction, necessity over conjunction, and a constructor over disjunction in each
argument. -/

/-- Possibility distributes over disjunction (`dia` preserves joins). -/
theorem dia_disj (p : Presentation) (A B : Pred) :
    Pred.dia p (Pred.disj A B) = Pred.disj (Pred.dia p A) (Pred.dia p B) := by
  funext t
  simp only [Pred.dia, Pred.disj]
  apply propext
  constructor
  · rintro ⟨t', hr, hA | hB⟩
    exacts [Or.inl ⟨t', hr, hA⟩, Or.inr ⟨t', hr, hB⟩]
  · rintro (⟨t', hr, hA⟩ | ⟨t', hr, hB⟩)
    exacts [⟨t', hr, Or.inl hA⟩, ⟨t', hr, Or.inr hB⟩]

/-- Necessity distributes over conjunction (`box` preserves meets). -/
theorem box_conj (p : Presentation) (A B : Pred) :
    Pred.box p (Pred.conj A B) = Pred.conj (Pred.box p A) (Pred.box p B) := by
  funext t
  simp only [Pred.box, Pred.conj]
  apply propext
  constructor
  · intro h; exact ⟨fun t' hr => (h t' hr).1, fun t' hr => (h t' hr).2⟩
  · rintro ⟨hA, hB⟩ t' hr; exact ⟨hA t' hr, hB t' hr⟩

/-- The spatial constructor distributes over disjunction in its first argument (the distributive law
    `delta` lifting a constructor over the Boolean structure). -/
theorem spatial_disj_left (l : Label) (A A' B : Pred) :
    Pred.spatial l (Pred.disj A A') B = Pred.disj (Pred.spatial l A B) (Pred.spatial l A' B) := by
  funext t
  apply propext
  cases t with
  | var _ => simp [Pred.spatial, Pred.disj]
  | subst _ _ _ => simp [Pred.spatial, Pred.disj]
  | sexp m args =>
      cases args with
      | nil => simp [Pred.spatial, Pred.disj]
      | cons a as =>
          cases as with
          | nil => simp [Pred.spatial, Pred.disj]
          | cons b bs =>
              cases bs with
              | nil => simp only [Pred.spatial, Pred.disj]; tauto
              | cons _ _ => simp [Pred.spatial, Pred.disj]

end MeTTaIL.OSLF
