/-
Module: MeTTaIL.Semantics.OSLF
Layer: Semantics
Purpose: Operational semantics in logical form (OSLF): a spatial-behavioral logic derived from a
  presentation, after Stay and Meredith, "Logic as a Distributive Law" (arXiv 1610.02247). They derive
  a type system for a calculus by combining the free Boolean algebra on terms with the calculus itself,
  `Form = BoolAlg + Calc`, and interpreting a formula as a set of terms via a distributive law
  `delta : Calc o BoolAlg => BoolAlg o Calc`. Here a formula's interpretation is a predicate on the
  MeTTaIL `AST` (the `Pred` type), the Boolean connectives are the set operations, the spatial
  composition is the calculus's constructors lifted by the distributive law (`Pred.spatial`, the
  concrete `delta`), and the behavioral modalities `dia`/`box` quantify over the reduction relation
  `RewStepMany`. The paper's two-hole-context possibly modal `[[ u<C>v ]] = { t | C[t,u] => v }` is
  `Pred.poss`, and its arrow-shaped bundling is `Pred.diaCtx`. The paper's per-term modal is the building
  block `poss`; the universal-over-inputs, existential-over-outputs `arrow`/`diaCtx` is the paper's
  informal type-level reading of `A -> B` ("given `u` of type `A`, `(t u)` evolves to a `v` of type
  `B`"), factored through `diaCtx_eq_poss`. The headline of the paper, that the lambda-calculus arrow type
  is the application-context instance of that possibly modal operator, is `arrow_eq_diaCtx` (the arrow is
  defined as that instance, so the equation is the `rfl` witnessing it). The soundness result is that a
  `box A` property (a safety property) is preserved by reduction (`box_preserved`); this is forward
  closure of `box` along the relation, not preservation of a typing judgment. As far as we know this is
  the first machine-checked formalization of the first-order spatial-behavioral fragment of OSLF for a
  calculus presentation (the Boolean and binary-spatial connectives and the behavioral modalities); the
  2-categorical distributive-law derivation and naturality are not formalized here. The
  greatest-fixed-point modalities live in `MeTTaILProofs.OSLFRec`.
Imports: MeTTaIL.Semantics.Eval (RewStep, RewStepMany and its transitivity)
Trusted boundary: none (fully proved)
Main exports: Pred and its connectives, spatial, dia, box, poss, diaCtx, arrow, arrow_eq_diaCtx,
  sat_spatial, dia_pred, box_preserved, box_eq_neg_dia_neg, safe, safe_preserved
Open obligations: the full 2-categorical distributive-law derivation remains outside this module; here
  the first-order spatial-behavioral fragment and its soundness are formalized.
-/
import MeTTaIL.Semantics.Eval

namespace MeTTaIL.OSLF

/-- The interpretation of a formula: the set of terms satisfying it, as a predicate on `AST`. Following
    Stay-Meredith we work with interpretations directly (`Form ==> BoolAlg o Calc` sends a formula to a
    subset of terms), and the connectives are operations on these predicates. -/
abbrev Pred := AST → Prop

namespace Pred

/-! ### The Boolean part (`BoolAlg`): formulae interpreted as set operations -/

/-- `top` holds of every term: `[[ T ]] = Calc(X)`. -/
def top : Pred := fun _ => True
/-- `bot` holds of no term: `[[ F ]] = empty`. -/
def bot : Pred := fun _ => False
/-- Conjunction is intersection: `[[ A and B ]] = [[A]] cap [[B]]`. -/
def conj (A B : Pred) : Pred := fun t => A t ∧ B t
/-- Disjunction is union: `[[ A or B ]] = [[A]] cup [[B]]`. -/
def disj (A B : Pred) : Pred := fun t => A t ∨ B t
/-- Negation is complement: `[[ not A ]] = Calc(X) - [[A]]`. -/
def neg (A : Pred) : Pred := fun t => ¬ A t

/-! ### The spatial part (`Calc`, via the distributive law `delta`)

The distributive law lifts a binary constructor `l` to predicates: a term satisfies the spatial
composition `spatial l A B` exactly when it is `(l a b)` with `a` of type `A` and `b` of type `B`. This
is the binary-constructor case of `delta : Calc o BoolAlg => BoolAlg o Calc`, `[[ A . B ]] =
Calc(.)([[A]] x [[B]])`; the general `n`-ary `delta` is not formalized here. -/

/-- Spatial composition under a binary constructor `l`: the terms `(l a b)` with `a` of type `A` and `b`
    of type `B`. -/
def spatial (l : Label) (A B : Pred) : Pred
  | .sexp m [a, b] => l = m ∧ A a ∧ B b
  | _ => False

/-! ### The behavioral part: modalities over the reduction relation -/

/-- Possibly (`dia`, the diamond): the term reduces to one satisfying `A`. -/
def dia (p : Presentation) (A : Pred) : Pred := fun t => ∃ t', RewStepMany p t t' ∧ A t'

/-- Necessarily (`box`): every reduct of the term satisfies `A`. -/
def box (p : Presentation) (A : Pred) : Pred := fun t => ∀ t', RewStepMany p t t' → A t'

/-- The Stay-Meredith pointwise possibly modal `[[ u<C>v ]] = { t | C[t,u] => v }`: with the two-hole
    context filled by `t` (the subject) and `u` (the partner), the result `ctx t u` reduces to `v`. -/
def poss (p : Presentation) (ctx : AST → AST → AST) (u v : AST) : Pred := fun t =>
  RewStepMany p (ctx t u) v

/-- The behavioral modality parametrized by a two-hole term context, bundled into an arrow shape: for
    every partner `u` of type `A`, the context `ctx t u` reduces to some `v` of type `B`. This is the
    general possibly modal operator of which the function arrow is an instance. -/
def diaCtx (p : Presentation) (ctx : AST → AST → AST) (A B : Pred) : Pred := fun t =>
  ∀ u, A u → ∃ v, RewStepMany p (ctx t u) v ∧ B v

/-- The behavioral arrow type `A -> B`: a term that, applied (via the application constructor `app`) to
    any argument of type `A`, reduces to a result of type `B`. The Stay-Meredith reading
    `alpha(u >-> v) = { t | (t u) => v }`, universally over inputs of type `A` and existentially over
    outputs of type `B`. -/
def arrow (p : Presentation) (app : Label) (A B : Pred) : Pred := fun t =>
  ∀ u, A u → ∃ v, RewStepMany p (.sexp app [t, u]) v ∧ B v

end Pred

open Pred

/-! ## The headline: the arrow type is a special case of the possibly modal operator

This is the central observation of "Logic as a Distributive Law": the function arrow falls out of the
general behavioral modality when the two-hole context is the application context `C = (- -)`. Here it
holds definitionally. -/

/-- The arrow type is the context-possibly modal for the application context, the Stay-Meredith reading:
    `A -> B` is `diaCtx` with `ctx t u = (app t u)`. The arrow is defined as exactly that instance, so the
    equation is the `rfl` that witnesses "the application-context possibly modal is the arrow". -/
theorem arrow_eq_diaCtx (p : Presentation) (app : Label) (A B : Pred) :
    arrow p app A B = diaCtx p (fun t u => .sexp app [t, u]) A B := rfl

/-- `diaCtx` reformulated through the pointwise possibly modal `poss`: for every partner `u` of type
    `A`, there is an output `v` of type `B` with `t` satisfying the possibly modal `u<C>v`. -/
theorem diaCtx_eq_poss (p : Presentation) (ctx : AST → AST → AST) (A B : Pred) (t : AST) :
    diaCtx p ctx A B t ↔ ∀ u, A u → ∃ v, B v ∧ poss p ctx u v t := by
  unfold diaCtx poss
  constructor
  · intro h u hu; obtain ⟨v, hv, hBv⟩ := h u hu; exact ⟨v, hBv, hv⟩
  · intro h u hu; obtain ⟨v, hBv, hv⟩ := h u hu; exact ⟨v, hv, hBv⟩

/-! ## Interpretation laws (the `BoolAlg` and spatial structure) -/

/-- The spatial composition is characterized exactly as the distributive law dictates: `(l a b)`
    satisfies `spatial l A B` iff `a` satisfies `A` and `b` satisfies `B`. -/
theorem sat_spatial (l : Label) (A B : Pred) (a b : AST) :
    spatial l A B (.sexp l [a, b]) ↔ A a ∧ B b := by
  simp [spatial]

/-- Conjunction is intersection. -/
theorem sat_conj (A B : Pred) (t : AST) : conj A B t ↔ A t ∧ B t := Iff.rfl
/-- Disjunction is union. -/
theorem sat_disj (A B : Pred) (t : AST) : disj A B t ↔ A t ∨ B t := Iff.rfl

/-! ## Behavioral soundness -/

/-- The diamond is closed under taking reduction-predecessors: if `t` reduces to `t'` and `t'` can reach
    an `A`-state, so can `t`. -/
theorem dia_pred (p : Presentation) (A : Pred) {t t' : AST} (h : RewStepMany p t t') :
    dia p A t' → dia p A t := by
  rintro ⟨u, hu, hAu⟩
  exact ⟨u, h.trans hu, hAu⟩

/-- `box`-properties are preserved by reduction (forward closure of `box` along the relation): if every
    reduct of `t` satisfies `A`, then so does every reduct of any reduct `t'` of `t`. A safety property
    expressed as `box A` in the logic is kept by the runtime as it reduces. This is the soundness of the
    behavioral modality against reduction, not preservation of a typing judgment. -/
theorem box_preserved (p : Presentation) (A : Pred) {t t' : AST} (h : RewStepMany p t t') :
    box p A t → box p A t' := by
  intro hbox u hu
  exact hbox u (h.trans hu)

/-- `box` and `dia` are De Morgan duals over the reduction relation: `box A = not (dia (not A))`. Uses
    classical reasoning for the inner double negation. -/
theorem box_eq_neg_dia_neg (p : Presentation) (A : Pred) :
    box p A = neg (dia p (neg A)) := by
  funext t
  apply propext
  unfold box neg dia
  constructor
  · intro hbox hdia
    obtain ⟨t', hstep, hnA⟩ := hdia
    exact hnA (hbox t' hstep)
  · intro h t' hstep
    rcases Classical.em (A t') with hA | hnA
    · exact hA
    · exact absurd ⟨t', hstep, hnA⟩ h

/-! ## Safety and liveness, expressed in the logic

The paper expresses confinement and liveness for the reflective higher-order pi calculus as formulae.
Their general shapes are the behavioral modalities: a safety property "never reach a bad state" is
`box (not Bad)`, and a liveness property "can reach a good state" is `dia Good`. Safety is preserved by
the runtime. The recursive greatest-fixed-point versions are future work. -/

/-- A safety property: the term never reduces to a `Bad` state. -/
def safe (p : Presentation) (Bad : Pred) : Pred := box p (neg Bad)

/-- A liveness property: the term can reduce to a `Good` state. -/
def live (p : Presentation) (Good : Pred) : Pred := dia p Good

/-- Safety is preserved by reduction: a safe term stays safe as the runtime reduces it. Immediate from
    behavioral subject reduction. -/
theorem safe_preserved (p : Presentation) (Bad : Pred) {t t' : AST} (h : RewStepMany p t t') :
    safe p Bad t → safe p Bad t' :=
  box_preserved p (neg Bad) h

end MeTTaIL.OSLF
