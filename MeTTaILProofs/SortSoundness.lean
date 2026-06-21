/-
Module: MeTTaILProofs.SortSoundness
Layer: Proofs
Purpose: Discharging the `SortPreserving` side-condition of `Semantics/Sorts`. That module proves head-sort
  preservation under reduction *given* that every base reduction keeps the head category; here we show
  that hypothesis follows from a checkable condition on the rules and instantiate it on a concrete
  presentation, so the head-sort preservation chain is no longer an uninstantiated schema. The key step is
  the matcher head-inversion `matchPat_sexp_head` (a match against a constructor-headed pattern forces the
  same head), which needs `LawfulBEq Label` from `MeTTaILProofs/DecEq` to read the matcher's `==`. With
  the right-hand-side half already in `Sorts` (`headCat_inst_sexp`), `sortPreserving_of_rulesHeadCatOk`
  gives `SortPreserving` from the per-rule head-category check `RulesHeadCatOk`, which is exactly what the
  elaborator's `checkRewrite` enforces. `demoPres` is a worked presentation with populated `terms`, proven
  `SortPreserving`, with `eval` shown to keep a concrete reduction at its sort.
Imports: MeTTaIL.Semantics.Sorts, MeTTaIL.Semantics.Relation (Reduces), MeTTaILProofs.DecEq (LawfulBEq)
Trusted boundary: none (fully proved)
Main exports: matchPat_sexp_head, headCat_of_matchPat, RulesHeadCatOk, sortPreserving_of_rulesHeadCatOk,
  demoPres, sortPreserving_demoPres
Open obligations: a recursive all-subterms well-sortedness still needs the full substitution lemma.
-/
import MeTTaIL.Semantics.Sorts
import MeTTaIL.Semantics.Relation
import MeTTaILProofs.DecEq

namespace MeTTaIL

/-- Matcher head-inversion: a successful match against a constructor-headed pattern `(l ps)` forces the
    matched term to have the same head `l`. Uses `LawfulBEq Label` to turn the matcher's `l == m` into
    `l = m`. -/
theorem matchPat_sexp_head {l : Label} {ps : List AST} {t : AST} {bnds bnds' : List (String × AST)}
    (h : AST.matchPat (.sexp l ps) t bnds = some bnds') : ∃ ts, t = .sexp l ts := by
  cases t with
  | var x => simp [AST.matchPat] at h
  | subst b r v => simp [AST.matchPat] at h
  | sexp m ts =>
      simp only [AST.matchPat] at h
      split at h
      · rename_i hlm; exact ⟨ts, by rw [eq_of_beq hlm]⟩
      · simp at h

/-- A matched term has the same head category as the (constructor-headed) pattern it matched. -/
theorem headCat_of_matchPat {defs : List Rule} {l : Label} {ps : List AST} {t : AST}
    {bnds bnds' : List (String × AST)} (h : AST.matchPat (.sexp l ps) t bnds = some bnds') :
    AST.headCat defs t = AST.headCat defs (.sexp l ps) := by
  obtain ⟨ts, rfl⟩ := matchPat_sexp_head h
  simp [AST.headCat]

/-- The per-rule head-category check: every rewrite's conclusion has constructor-headed sides whose head
    categories agree. This is the semantic content of `checkRewrite`'s `catCompatible` test restricted to
    determined (non-variable) heads, and it is exactly what is needed to discharge `SortPreserving`. -/
def RulesHeadCatOk (p : Presentation) : Prop :=
  ∀ rd ∈ p.rewrites, ∃ l ps lr rps, rd.rw.conclusion = (.sexp l ps, .sexp lr rps) ∧
    AST.headCat p.terms (.sexp l ps) = AST.headCat p.terms (.sexp lr rps)

/-- Discharging `SortPreserving` from the checkable per-rule condition: if every rule keeps the head
    category between its conclusion's two constructor-headed sides, every base reduction does, so the whole
    reduction relation preserves the head sort. The matched redex has the left head category
    (`headCat_of_matchPat`), the contractum has the right head category (`headCat_inst_sexp`), and the rule
    condition equates them. -/
theorem sortPreserving_of_rulesHeadCatOk {p : Presentation} (h : RulesHeadCatOk p) :
    SortPreserving p := by
  intro t t' hred
  cases hred with
  | step rd bnds bnds' hmem hmatch _ heq =>
      obtain ⟨l, ps, lr, rps, hconc, hcat⟩ := h rd hmem
      rw [hconc] at hmatch heq
      -- hmatch : matchPat (.sexp l ps) t [] = some bnds ; heq : t' = inst bnds' (.sexp lr rps)
      have ht : AST.headCat p.terms t = AST.headCat p.terms (.sexp l ps) := headCat_of_matchPat hmatch
      have ht' : AST.headCat p.terms t' = AST.headCat p.terms (.sexp lr rps) := by
        rw [heq]; exact headCat_inst_sexp p.terms bnds' lr rps
      rw [ht, ht', hcat]

/-! ## A worked instance: head-sort preservation on a concrete presentation

`demoPres` declares a sort `T`, the constants `a`, `b`, and a unary `f`, with the single rewrite
`(f a) ~> b`. Its `terms` give every operator the category `T`, so the rule keeps the head category, and
`SortPreserving demoPres` follows from the criterion. -/

private def tmC : Cat := .idCat "T"
private def rl (n : String) (items : List Item) : Rule := { label := .id n, cat := tmC, items := items }

/-- A small presentation with populated grammar and one head-sort-preserving rule. -/
def demoPres : Presentation :=
  .mk [tmC] [rl "a" [], rl "b" [], rl "f" [.nterminal tmC]] []
    [ { name := "r", rw := .base (.sexp (.id "f") [.sexp (.id "a") []]) (.sexp (.id "b") []) } ] []

theorem rulesHeadCatOk_demoPres : RulesHeadCatOk demoPres := by
  intro rd hrd
  simp only [demoPres, Presentation.rewrites, List.mem_singleton] at hrd
  subst hrd
  exact ⟨.id "f", [.sexp (.id "a") []], .id "b", [], rfl, rfl⟩

/-- The concrete presentation preserves the head sort under reduction. -/
theorem sortPreserving_demoPres : SortPreserving demoPres :=
  sortPreserving_of_rulesHeadCatOk rulesHeadCatOk_demoPres

/-- And so its normalizer keeps a term at its head sort: `(f a)` and its normal form share a category. -/
example : AST.headCat demoPres.terms (eval demoPres 100 (.sexp (.id "f") [.sexp (.id "a") []]))
    = AST.headCat demoPres.terms (.sexp (.id "f") [.sexp (.id "a") []]) :=
  eval_preserves_headCat sortPreserving_demoPres 100 _

end MeTTaIL
