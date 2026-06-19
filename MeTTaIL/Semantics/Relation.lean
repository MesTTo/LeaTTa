/-
The GSLT reduction relation: a presentation's rewrites induce reduction on terms.

`Reduces p t t'` holds when some rewrite of `p` fires on `t`: its conclusion's left-hand side matches
`t` (binding the pattern variables), each premise `src ~> tgt` requires the bound `src` subterm to
itself reduce (binding `tgt` to the reduct), and the contractum is the conclusion's right-hand side
instantiated with the bindings. Base rewrites (no premises) reduce a redex directly; premised
rewrites are the congruence/context rules (par1, par2, RNew, ...). This is the precise sense in which
"presentations of GSLTs describe the operational semantics of computational calculi."

The relation is built on the executable matcher/instantiator of `Semantics/Reduce.lean`. The final
theorem links the two: every reduct the executable `applyBaseRewrite` produces is a real reduction.
Mathlib-free.
-/
import MeTTaIL.Semantics.Reduce

namespace MeTTaIL

/-- The base identifier of a dotted path: the variable name a premise binds. -/
def DottedPath.baseName : DottedPath → String
  | .base n => n
  | .qualified n _ => n

/-- The premises (the `let h in ...` hypotheses) of a rewrite, outermost first. -/
def Rewrite.premises : Rewrite → List Hyp
  | .base _ _ => []
  | .ctx h r => h :: Rewrite.premises r

mutual
  /-- One-step reduction induced by a presentation's rewrites. -/
  inductive Reduces (p : Presentation) : AST → AST → Prop where
    | step {t t' : AST} (rd : RewriteDecl) (bnds bnds' : List (String × AST)) :
        rd ∈ p.rewrites →
        AST.matchPat rd.rw.conclusion.1 t [] = some bnds →
        PremisesHold p rd.rw.premises bnds bnds' →
        t' = AST.inst bnds' rd.rw.conclusion.2 →
        Reduces p t t'
  /-- The premises of a rewrite hold under the current bindings, extending them with each premise's
      target binding (the reduct of its source). -/
  inductive PremisesHold (p : Presentation) :
      List Hyp → List (String × AST) → List (String × AST) → Prop where
    | nil {bnds : List (String × AST)} : PremisesHold p [] bnds bnds
    | cons {h : Hyp} {hs : List Hyp} {bnds rest : List (String × AST)} {B : AST} :
        Reduces p (AST.inst bnds (.var h.src)) B →
        PremisesHold p hs ((h.tgt.baseName, B) :: bnds) rest →
        PremisesHold p (h :: hs) bnds rest
end

/-- Many-step reduction: the reflexive-transitive closure of `Reduces`. -/
inductive ReducesMany (p : Presentation) : AST → AST → Prop where
  | refl {t : AST} : ReducesMany p t t
  | tail {t u v : AST} : ReducesMany p t u → Reduces p u v → ReducesMany p t v

/-- A single reduction is a one-step reduction sequence. -/
theorem ReducesMany.single {p : Presentation} {t t' : AST} (h : Reduces p t t') :
    ReducesMany p t t' := .tail .refl h

/-- Many-step reduction is transitive. -/
theorem ReducesMany.trans {p : Presentation} {t u v : AST}
    (h₁ : ReducesMany p t u) (h₂ : ReducesMany p u v) : ReducesMany p t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ s ih => exact .tail ih s

/-- A base rewrite (no premises) whose left-hand side matches `t` reduces `t` to the instantiated
    right-hand side. -/
theorem reduces_base (p : Presentation) (rd : RewriteDecl) (lhs rhs t : AST)
    (bnds : List (String × AST))
    (hmem : rd ∈ p.rewrites) (hrw : rd.rw = .base lhs rhs)
    (hmatch : AST.matchPat lhs t [] = some bnds) :
    Reduces p t (AST.inst bnds rhs) :=
  Reduces.step rd bnds bnds hmem
    (by simp only [hrw, Rewrite.conclusion]; exact hmatch)
    (by simp only [hrw, Rewrite.premises]; exact PremisesHold.nil)
    (by simp only [hrw, Rewrite.conclusion])

/-- The executable matcher is sound for the reduction relation: every reduct that `applyBaseRewrite`
    produces from a rewrite of `p` is a genuine one-step reduction. -/
theorem reduces_of_applyBaseRewrite (p : Presentation) (rd : RewriteDecl) (t t' : AST)
    (hmem : rd ∈ p.rewrites) (h : applyBaseRewrite rd t = some t') :
    Reduces p t t' := by
  cases hrw : rd.rw with
  | base lhs rhs =>
      simp [applyBaseRewrite, hrw] at h
      obtain ⟨bnds, hm, heq⟩ := h
      exact heq ▸ reduces_base p rd lhs rhs t bnds hmem hrw hm
  | ctx hyp r => simp [applyBaseRewrite, hrw] at h

end MeTTaIL
