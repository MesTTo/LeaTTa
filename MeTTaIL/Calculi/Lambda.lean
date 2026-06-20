/-
Module: MeTTaIL.Calculi.Lambda
Layer: Calculi
Purpose: Simply-typed lambda calculus (STLC) with de Bruijn indices, the binder-calculus
  type-soundness companion to `MeTTaIL/Calculi/SKI.lean`. SKI handles the binder-free case, where
  typing and reduction are first-order; here the calculus has a binder (`lam`), so reduction needs
  capture-avoiding substitution and typing needs a context. A `var i` is the binder `i` levels out, the
  typing context `Γ : List Ty` lists the binder types innermost first, and `var i` looks up `Γ[i]?`. The
  two soundness results are the standard pair: `preservation` (subject reduction) says reduction keeps
  the type, resting on a substitution lemma and a context-weakening lemma; `progress` says a closed,
  well-typed term is a value (a `lam`) or can take a step, so it never gets stuck. The de Bruijn index
  arithmetic is handled with `omega` and the core `List.getElem?`/`List.insertIdx` lemmas.
Imports: none (Mathlib-free)
Trusted boundary: human-reviewed spec
Main exports: Ty, Tm, shift, subst, Step, HasTy, Value, weakening, subst_hasTy, preservation, progress
Open obligations: none
-/

namespace MeTTaIL.STLC

/-- Simple types: base types (indexed by a `Nat`) and function types. Same shape as the SKI `Ty`. -/
inductive Ty where
  | base (n : Nat)
  | arr (dom cod : Ty)
deriving DecidableEq, Repr, Inhabited

/-- Lambda terms in de Bruijn form. A `var i` refers to the binder `i` levels out (0 is the nearest
    enclosing `lam`). A `lam ty body` binds one fresh variable of type `ty`. -/
inductive Tm where
  | var (i : Nat)
  | lam (ty : Ty) (body : Tm)
  | app (fn arg : Tm)
deriving DecidableEq, Repr, Inhabited

/-- de Bruijn shift (lifting): add `d` to every free variable whose index is at least the cutoff `c`.
    Crossing a `lam` raises the cutoff by one, because that binder introduces a new index 0 and pushes
    the outer variables out by one. This is the weakening operation on terms. -/
def shift (d c : Nat) : Tm → Tm
  | .var i => if i < c then .var i else .var (i + d)
  | .lam ty body => .lam ty (shift d (c + 1) body)
  | .app fn arg => .app (shift d c fn) (shift d c arg)

/-- Capture-avoiding single-variable substitution `t[j := s]`: replace the variable with index `j` by
    `s`, drop the indices above `j` by one (they lose the binder that `j` named), and leave the indices
    below `j` alone. Crossing a `lam` raises the target index to `j+1` and shifts `s` up by one so its
    free variables still point at the same binders. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | .var i => if i < j then .var i else if i = j then s else .var (i - 1)
  | .lam ty body => .lam ty (subst (j + 1) (shift 1 0 s) body)
  | .app fn arg => .app (subst j s fn) (subst j s arg)

/-- `t[j := s]` notation for de Bruijn substitution. -/
notation:max t "[" j " := " s "]" => subst j s t

/-- One-step reduction. The beta rule contracts a redex `(λ : ty. b) s` to `b[0 := s]`; the three
    congruence rules let reduction happen under either side of an application and under a `lam`. -/
inductive Step : Tm → Tm → Prop where
  | beta {ty b s} : Step (.app (.lam ty b) s) (b[0 := s])
  | appL {f f' a} : Step f f' → Step (.app f a) (.app f' a)
  | appR {f a a'} : Step a a' → Step (.app f a) (.app f a')
  | lam {ty b b'} : Step b b' → Step (.lam ty b) (.lam ty b')

/-- The typing relation, with a de Bruijn context `Γ : List Ty` (the binder types, innermost first).
    A variable's type is read off the context at its index; `lam` extends the context with the bound
    type; `app` is the usual arrow elimination. -/
inductive HasTy : List Ty → Tm → Ty → Prop where
  | var {Γ i T} : Γ[i]? = some T → HasTy Γ (.var i) T
  | lam {Γ ty b cod} : HasTy (ty :: Γ) b cod → HasTy Γ (.lam ty b) (.arr ty cod)
  | app {Γ f a dom cod} : HasTy Γ f (.arr dom cod) → HasTy Γ a dom → HasTy Γ (.app f a) cod

/-- A value is a (weak head) normal form we stop at. With only functions, the values are the lambda
    abstractions. -/
def Value : Tm → Prop
  | .lam _ _ => True
  | _ => False

/-- Decidable test for the `Value` predicate, used to phrase progress. -/
def isLam : Tm → Bool
  | .lam _ _ => true
  | _ => false

/-- `isLam` decides `Value`: it is `true` exactly for the lambda values. -/
theorem isLam_iff_value {t : Tm} : isLam t = true ↔ Value t := by
  cases t <;> simp [isLam, Value]

/-!
### Weakening

Inserting a fresh binding of type `A` at position `c` of the context, and shifting the term's free
variables across that new binder, preserves typing. The proof is an induction on the typing
derivation; the only real work is the `var` case, where the cutoff `c` splits the index into the part
below `c` (untouched) and the part at or above `c` (shifted up by one), matched by the core
`List.insertIdx` lookup lemmas.
-/

/-- Context weakening: inserting a binding at position `c` and shifting across it preserves typing. -/
theorem weakening {Γ : List Ty} {t : Tm} {T : Ty}
    (h : HasTy Γ t T) : ∀ (c : Nat) (A : Ty), HasTy (Γ.insertIdx c A) (shift 1 c t) T := by
  induction h with
  | @var Γ i T hlk =>
      intro c A
      simp only [shift]
      by_cases hic : i < c
      · -- index below the cutoff: unchanged, and the lookup is unaffected by the later insertion.
        rw [if_pos hic]
        exact .var (by rw [List.getElem?_insertIdx_of_lt hic]; exact hlk)
      · -- index at or above the cutoff: shifted up by one, matching the inserted slot.
        rw [if_neg hic]
        refine .var ?_
        rw [List.getElem?_insertIdx_of_gt (by omega)]
        simpa using hlk
  | @lam Γ ty b cod _ ih =>
      intro c A
      simp only [shift]
      exact .lam (by
        have := ih (c + 1) A
        rwa [List.insertIdx_succ_cons] at this)
  | app _ _ ihf iha =>
      intro c A
      simp only [shift]
      exact .app (ihf c A) (iha c A)

/-- Weakening at the front of the context: the common special case `c = 0`, where inserting at
    position 0 is just a `cons`. This is what the substitution lemma needs to push `s` under a `lam`. -/
theorem weakening0 {Γ : List Ty} {s : Tm} {A B : Ty}
    (h : HasTy Γ s A) : HasTy (B :: Γ) (shift 1 0 s) A := by
  have := weakening h 0 B
  rwa [List.insertIdx_zero] at this

/-!
### Substitution

If `s` has type `A` in `Γ`, and `t` has type `B` in the context `Γ` with `A` inserted at position
`j`, then `t[j := s]` has type `B` in `Γ`. The induction is on the term `t`, generalizing the context,
the position `j`, the substituend `s`, and the result type `B` (all of these change under the `lam`
case). The `var` case is again the heart of it: the index is below, equal to, or above the inserted
slot, handled by the three `List.insertIdx` lookup lemmas plus `omega`.
-/

/-- The de Bruijn substitution lemma. -/
theorem subst_hasTy {A : Ty} : ∀ {Γ : List Ty} {t : Tm} {j : Nat} {s : Tm} {B : Ty},
    HasTy Γ s A → HasTy (Γ.insertIdx j A) t B → HasTy Γ (t[j := s]) B := by
  intro Γ t
  induction t generalizing Γ with
  | var i =>
      intro j s B hs ht
      cases ht with
      | var hlk =>
          simp only [subst]
          by_cases hij : i < j
          · -- below the inserted slot: the variable is unchanged and the slot does not move it.
            rw [if_pos hij]
            rw [List.getElem?_insertIdx_of_lt hij] at hlk
            exact .var hlk
          · rw [if_neg hij]
            by_cases hej : i = j
            · -- exactly the inserted slot: the variable becomes `s`, whose type `A` equals `B`.
              subst hej
              rw [if_pos rfl]
              rw [List.getElem?_insertIdx_self] at hlk
              by_cases hlen : i ≤ Γ.length
              · rw [if_pos hlen] at hlk
                simp only [Option.some.injEq] at hlk
                subst hlk
                exact hs
              · rw [if_neg hlen] at hlk
                exact absurd hlk (by simp)
            · -- above the inserted slot: the variable drops by one, matching the shifted context.
              rw [if_neg hej]
              refine .var ?_
              rw [List.getElem?_insertIdx_of_gt (by omega)] at hlk
              exact hlk
  | lam ty body ih =>
      intro j s B hs ht
      cases ht with
      | @lam _ _ _ cod hbody =>
          simp only [subst]
          refine .lam ?_
          have hs' : HasTy (ty :: Γ) (shift 1 0 s) A := weakening0 hs
          have hbody' : HasTy ((ty :: Γ).insertIdx (j + 1) A) body cod := by
            rwa [List.insertIdx_succ_cons]
          exact ih hs' hbody'
  | app fn arg ihf iha =>
      intro j s B hs ht
      cases ht with
      | app hf ha =>
          simp only [subst]
          exact .app (ihf hs hf) (iha hs ha)

/-- Substitution at the front of the context: the `j = 0` special case, where the inserted context is
    a `cons`. This is exactly the shape the beta rule produces. -/
theorem subst0_hasTy {Γ : List Ty} {b s : Tm} {A B : Ty}
    (hs : HasTy Γ s A) (hb : HasTy (A :: Γ) b B) : HasTy Γ (b[0 := s]) B := by
  have hb' : HasTy (Γ.insertIdx 0 A) b B := by rwa [List.insertIdx_zero]
  exact subst_hasTy hs hb'

/-!
### Soundness

`preservation` is subject reduction: a step keeps the type. The beta case is the substitution lemma;
the three congruence cases recurse. `progress` says a closed well-typed term is a value or steps, so
typing rules out stuck closed terms.
-/

/-- Subject reduction (type preservation): a single reduction step preserves the type. The context is
    generalized because the `lam` congruence rule descends under a binder, extending the context. -/
theorem preservation {t t' : Tm} (hs : Step t t') :
    ∀ {Γ : List Ty} {T : Ty}, HasTy Γ t T → HasTy Γ t' T := by
  induction hs with
  | beta =>
      intro Γ T ht
      cases ht with
      | app hlam harg =>
          cases hlam with
          | lam hbody => exact subst0_hasTy harg hbody
  | appL _ ih =>
      intro Γ T ht
      cases ht with
      | app hf ha => exact .app (ih hf) ha
  | appR _ ih =>
      intro Γ T ht
      cases ht with
      | app hf ha => exact .app hf (ih ha)
  | lam _ ih =>
      intro Γ T ht
      cases ht with
      | lam hbody => exact .lam (ih hbody)

/-- Progress: a closed, well-typed term is either a value (a `lam`) or it can take a step. So a closed
    well-typed term is never stuck. The induction is on the typing derivation in the empty context; the
    `var` case is impossible (no variable types in the empty context) and the `app` case branches on
    whether the function part is already a value, exposing a beta redex, or can step. -/
theorem progress {t : Tm} {T : Ty} (ht : HasTy [] t T) :
    Value t ∨ ∃ t', Step t t' := by
  generalize hΓ : ([] : List Ty) = Γ at ht
  induction ht with
  | @var Γ i T hlk =>
      subst hΓ
      simp at hlk
  | lam _ _ =>
      exact Or.inl trivial
  | @app Γ f a dom cod hf ha ihf _ =>
      subst hΓ
      rcases ihf rfl with hfval | ⟨f', hf'⟩
      · -- the function is a value, hence a `lam`, so the application is a beta redex.
        match f, hfval, hf with
        | .lam ty b, _, _ => exact Or.inr ⟨b[0 := a], .beta⟩
      · -- the function steps, so the application steps on its left.
        exact Or.inr ⟨.app f' a, .appL hf'⟩

/-!
### Examples

A few concrete closed terms exercising the two theorems. We write `idTm` for the identity at a chosen
type and reduce `(λ x. x) (λ y. y)`.
-/

/-- The identity function at type `T -> T`: `λ (x : T). x`. -/
def idTm (T : Ty) : Tm := .lam T (.var 0)

/-- The identity is well typed at `T -> T` in any context. -/
example (T : Ty) : HasTy [] (idTm T) (.arr T T) :=
  .lam (.var rfl)

/-- `(λ x. x) (λ y. y)` at base type `0`: the outer identity expects an argument of type `b0 -> b0`,
    and the inner identity supplies one. -/
example :
    HasTy [] (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0)))
      (.arr (.base 0) (.base 0)) :=
  .app (.lam (.var rfl)) (.lam (.var rfl))

/-- That application beta-reduces to the inner identity. The substitution `(var 0)[0 := idTm _]`
    computes to `idTm _`. -/
example :
    Step (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0))) (idTm (.base 0)) := by
  have h : Step (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0)))
      ((Tm.var 0)[0 := idTm (.base 0)]) := .beta
  simpa [subst, idTm] using h

/-- Preservation in action: the reduct keeps the type `b0 -> b0`. -/
example
    (ht : HasTy [] (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0)))
      (.arr (.base 0) (.base 0))) :
    HasTy [] (idTm (.base 0)) (.arr (.base 0) (.base 0)) := by
  have hstep : Step (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0))) (idTm (.base 0)) := by
    have h : Step (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0)))
        ((Tm.var 0)[0 := idTm (.base 0)]) := .beta
    simpa [subst, idTm] using h
  exact preservation hstep ht

/-- Progress in action: the well-typed redex `(λ x. x) (λ y. y)` is not a value, so progress gives a
    step. -/
example :
    ∃ t', Step (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0))) t' := by
  have ht : HasTy [] (.app (idTm (.arr (.base 0) (.base 0))) (idTm (.base 0)))
      (.arr (.base 0) (.base 0)) :=
    .app (.lam (.var rfl)) (.lam (.var rfl))
  rcases progress ht with hval | hstep
  · exact absurd hval (by simp [Value])
  · exact hstep

end MeTTaIL.STLC
