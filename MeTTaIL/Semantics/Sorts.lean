/-
Module: MeTTaIL.Semantics.Sorts
Layer: Semantics
Purpose: The head-sort discipline a presentation induces, and its preservation under reduction. The
  presentation's grammar (its `terms`, the function symbols written as rules `label . cat ::= items`)
  assigns each constructor a result category; `AST.headCat` reads off the category of a term's outermost
  constructor only (it is `none` for a variable or a head that names no rule). This is a shallow
  invariant, the *head* sort, not a full typing judgment about all subterms. The result is preservation:
  if every base reduction keeps the head category (`SortPreserving`, the semantic content of the
  `checkRewrite` category check the elaborator enforces), then the whole context-closed relation keeps it
  (`rewStep_preserves_headCat`), and so do many-step reduction and the normalizer
  (`rewStepMany_preserves_headCat`, `eval_preserves_headCat`). So a term keeps its head sort as the
  runtime reduces it. `SortPreserving` is an assumed side-condition: it is satisfiable
  (`sortPreserving_of_no_rewrites`), and discharging it on a presentation amounts to checking each rule
  preserves the head category. `headCat_inst_sexp` proves the right-hand-side half of that substitution
  lemma (instantiation keeps a constructor head); the left-hand-side half (a match against a
  constructor-headed pattern forces the same head) is the matcher head-inversion, which needs
  `LawfulBEq Label`. Both halves are assembled in `MeTTaILProofs.SortSoundness`, which proves the
  checkable per-rule criterion `sortPreserving_of_rulesHeadCatOk` discharges `SortPreserving` and
  instantiates it on a concrete presentation.

  This is *not* a full type system. The genuine, richer type-soundness proofs live in `Calculi.SKI` and
  `Calculi.Lambda`, which are separate, self-contained developments over their own term types (`CL`,
  `Tm`) and do not refine this head-sort discipline. The modal / spatial-behavioral OSLF logic is in
  `Semantics.OSLF`.
Imports: MeTTaIL.Semantics.Eval (RewStep, RewStepMany, eval, eval_sound), MeTTaIL.Theory.Check (headCat)
Trusted boundary: none (fully proved)
Main exports: SortPreserving, rewStep_preserves_headCat, rewStepMany_preserves_headCat,
  eval_preserves_headCat, sortPreserving_of_no_rewrites, headCat_inst_sexp
Open obligations: a recursive all-subterms well-sortedness needs the full substitution lemma (the
  head-sort version is discharged in `MeTTaILProofs.SortSoundness`).
-/
import MeTTaIL.Semantics.Eval
import MeTTaIL.Theory.Check

namespace MeTTaIL

/-- A presentation's reductions are head-sort-preserving when every base reduction keeps the head
    category, the sort of the term's outermost constructor. This is the semantic content of the category
    check in `checkRewrite` (which requires a rule's two sides to have compatible categories): firing a
    rule does not change the head sort. An assumed side-condition here (see `sortPreserving_of_no_rewrites`
    for satisfiability and `headCat_inst_sexp` for half of the discharge). -/
def SortPreserving (p : Presentation) : Prop :=
  ∀ t t', Reduces p t t' → AST.headCat p.terms t = AST.headCat p.terms t'

/-- Head-sort preservation under the full context-closed relation: if base reductions keep the head
    category, so does `RewStep`. The congruence cases hold structurally: a step inside a `sexp` argument
    keeps the operator, hence its category; a step inside a `Subst` keeps the body that determines the
    category. -/
theorem rewStep_preserves_headCat {p : Presentation} (h : SortPreserving p) {t t' : AST}
    (hstep : RewStep p t t') : AST.headCat p.terms t = AST.headCat p.terms t' := by
  induction hstep with
  | top hred => exact h _ _ hred
  | arg _ _ => simp [AST.headCat]
  | substB _ ih => simp only [AST.headCat]; exact ih
  | substR _ _ => simp [AST.headCat]

/-- Many-step reduction preserves the head category. -/
theorem rewStepMany_preserves_headCat {p : Presentation} (h : SortPreserving p) {t t' : AST}
    (hm : RewStepMany p t t') : AST.headCat p.terms t = AST.headCat p.terms t' := by
  induction hm with
  | refl => rfl
  | tail _ s ih => exact ih.trans (rewStep_preserves_headCat h s)

/-- The normalizer preserves the head category: `eval` keeps a term at its head sort, via `eval_sound`. -/
theorem eval_preserves_headCat {p : Presentation} (h : SortPreserving p) (fuel : Nat) (t : AST) :
    AST.headCat p.terms (eval p fuel t) = AST.headCat p.terms t :=
  (rewStepMany_preserves_headCat h (eval_sound p fuel t)).symm

/-- `SortPreserving` is satisfiable: a presentation with no rewrite rules preserves the head sort
    vacuously, since nothing reduces. So the conditional preservation theorems are not empty. -/
theorem sortPreserving_of_no_rewrites {p : Presentation} (hp : p.rewrites = []) : SortPreserving p := by
  intro _ _ hred
  cases hred with
  | step rd _ _ hmem _ _ _ => rw [hp] at hmem; exact absurd hmem (List.not_mem_nil)

/-- Instantiation preserves a constructor head category: substituting into a `sexp`-headed term keeps the
    head label, hence its category. This is the right-hand-side half of the substitution lemma that would
    discharge `SortPreserving` from a per-rule head-category check; the left-hand-side half (matching
    against a constructor-headed pattern forces the same head) awaits `LawfulBEq Label`. -/
theorem headCat_inst_sexp (defs : List Rule) (bnds : List (String × AST)) (l : Label) (args : List AST) :
    AST.headCat defs (AST.inst bnds (.sexp l args)) = AST.headCat defs (.sexp l args) := by
  simp [AST.inst, AST.headCat]

end MeTTaIL
