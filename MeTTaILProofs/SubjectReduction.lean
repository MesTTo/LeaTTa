/-
Module: MeTTaILProofs.SubjectReduction
Layer: Proofs
Purpose: The matching half of the substitution lemma, and subject reduction for the recursive sort
  system of `Semantics/WellSorted`. `WellSorted.inst_wellSorted` gives the inst half (instantiating a
  well-sorted term with a well-sorted substitution stays well-sorted); here we prove the matching half:
  matching a well-sorted subject against a well-sorted pattern produces a well-sorted substitution. The
  two halves combine into `subjectReduction_base`: a base rewrite whose two sides are well-sorted under a
  shared context keeps the subject well-sorted, so every subterm stays at its declared sort across a
  contraction. That preservation then lifts through the runtime's one-step relation `RewStep` and the
  many-step `RewStepMany` (`rewStep_preserves_wellSorted`, `rewStepMany_preserves_wellSorted`): the
  congruence cases hold structurally, and the `Subst` cases are vacuous because a well-sorted term is
  subst-free. So subject reduction holds along the whole reduction relation, given that base contractions
  preserve sorts (which `subjectReduction_base` supplies). This is the deep type-soundness result for the
  generic runtime, beyond the head-sort preservation of `Semantics/Sorts`. The matcher inversion
  `matchPat_sexp_head` (from `SortSoundness`) and `LawfulBEq AST`/`Label` (from `DecEq`) read the matcher's
  `==`.
Imports: MeTTaIL.Semantics.WellSorted, MeTTaILProofs.SortSoundness (matchPat_sexp_head, demoPres),
  MeTTaILProofs.DecEq (LawfulBEq)
Trusted boundary: none (fully proved)
Main exports: varsOf, LabelDeterminesRule, WSsub, matchPat_wssub, matchPat_cover, subjectReduction_base,
  rewStep_preserves_wellSorted, rewStepMany_preserves_wellSorted
Open obligations: the top-level hypothesis of the lifting (that base reductions of the `Reduces` relation,
  including premised rewrites, preserve sorts) is discharged by `subjectReduction_base` for premise-free
  well-sorted rules; binder/`Subst` handling (the first-order fragment is complete).
-/
import MeTTaIL.Semantics.WellSorted
import MeTTaILProofs.SortSoundness
import MeTTaILProofs.DecEq

namespace MeTTaIL

mutual
  /-- Free base-variable names of a term, in left-to-right order. -/
  def varsOf : AST → List String
    | .var (.base x) => [x]
    | .var _ => []
    | .sexp _ args => varsOfList args
    | .subst b r _ => varsOf b ++ varsOf r
  def varsOfList : List AST → List String
    | [] => []
    | a :: as => varsOf a ++ varsOfList as
end

/-- Grammar well-formedness: rules that share a label declare the same argument sorts. This is what lets
    a pattern and a matched subject, both headed by the same constructor, be aligned argument by argument. -/
def LabelDeterminesRule (p : Presentation) : Prop :=
  ∀ r₁ ∈ p.terms, ∀ r₂ ∈ p.terms, r₁.label = r₂.label → r₁.argSorts = r₂.argSorts

/-- The matcher's name lookup, projected to the bound term. -/
def bndLookup (bnds : List (String × AST)) (v : String) : Option AST :=
  (bnds.find? (fun b => b.1 == v)).map (·.2)

/-- `bnds` is a well-sorted substitution for `Δ` over `Γ`: each `Δ`-variable it binds is bound to a term
    that is well-sorted at that variable's sort. -/
def WSsub (p : Presentation) (Γ Δ : Ctx) (bnds : List (String × AST)) : Prop :=
  ∀ y ty cy, bndLookup bnds y = some ty → Δ.lookup y = some cy → WellSorted p Γ ty cy

/-- Looking up the freshly prepended variable returns its binding. -/
theorem bndLookup_cons_self (x : String) (t : AST) (bnds0 : List (String × AST)) :
    bndLookup ((x, t) :: bnds0) x = some t := by simp [bndLookup]

/-- Looking up a different variable skips the prepended binding. -/
theorem bndLookup_cons_of_ne {x y : String} (h : x ≠ y) (t : AST) (bnds0 : List (String × AST)) :
    bndLookup ((x, t) :: bnds0) y = bndLookup bnds0 y := by
  have hb : (x == y) = false := by simpa using h
  simp [bndLookup, hb]

/-! ### Inversions for the well-sortedness relation -/

/-- A well-sorted application reveals the rule that types it. -/
theorem wellSorted_sexp_inv {p : Presentation} {Γ : Ctx} {l : Label} {ts : List AST} {c : Cat}
    (h : WellSorted p Γ (.sexp l ts) c) :
    ∃ r, r ∈ p.terms ∧ r.label = l ∧ c = r.cat ∧ WellSortedList p Γ ts r.argSorts := by
  cases h with
  | sexp r hmem hlabel hargs => exact ⟨r, hmem, hlabel, rfl, hargs⟩

/-- A well-sorted argument list at the empty sort list is empty. -/
theorem wellSortedList_nil_inv {p : Presentation} {Γ : Ctx} {ts : List AST}
    (h : WellSortedList p Γ ts []) : ts = [] := by
  cases h with
  | nil => rfl

/-- A well-sorted nonempty argument list splits head and tail. -/
theorem wellSortedList_cons_inv {p : Presentation} {Γ : Ctx} {t : AST} {ts : List AST} {cs : List Cat}
    (h : WellSortedList p Γ (t :: ts) cs) :
    ∃ c cs', cs = c :: cs' ∧ WellSorted p Γ t c ∧ WellSortedList p Γ ts cs' := by
  cases h with
  | cons ha has => exact ⟨_, _, rfl, ha, has⟩

/-- A well-sorted argument list at a nonempty sort list splits, aligning head and head-sort. -/
theorem wellSortedList_cons_sort_inv {p : Presentation} {Γ : Ctx} {ts : List AST} {c : Cat}
    {cs' : List Cat} (h : WellSortedList p Γ ts (c :: cs')) :
    ∃ t' ts'', ts = t' :: ts'' ∧ WellSorted p Γ t' c ∧ WellSortedList p Γ ts'' cs' := by
  cases h with
  | cons ht hts => exact ⟨_, _, rfl, ht, hts⟩

/-- Replacing one argument of a well-sorted list by a same-sorted term keeps the list well-sorted. The
    replacement need only preserve sorts at whatever sort the original argument had. -/
theorem wellSortedList_arg_subst {p : Presentation} {Γ : Ctx} {a a' : AST}
    (ha : ∀ ca, WellSorted p Γ a ca → WellSorted p Γ a' ca) :
    ∀ {pre post : List AST} {cs : List Cat}, WellSortedList p Γ (pre ++ a :: post) cs →
      WellSortedList p Γ (pre ++ a' :: post) cs
  | [], _, _, hws => by
      obtain ⟨ca, _, rfl, hwa, hwpost⟩ := wellSortedList_cons_inv hws
      exact .cons (ha ca hwa) hwpost
  | _ :: _, _, _, hws => by
      obtain ⟨cx, _, rfl, hwx, hwrest⟩ := wellSortedList_cons_inv hws
      exact .cons hwx (wellSortedList_arg_subst ha hwrest)

/-- If a variable is bound, instantiation returns the bound term. -/
theorem inst_var_of_bndLookup {bnds : List (String × AST)} {v : String} {ty : AST}
    (h : bndLookup bnds v = some ty) : AST.inst bnds (.var (.base v)) = ty := by
  unfold bndLookup at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨pr, hpr, hpr2⟩ := h
  unfold AST.inst
  rw [hpr]
  exact hpr2

/-- Variable matching either leaves the bindings unchanged (a consistent re-match, so the variable was
    already bound) or prepends a new binding (so the variable was previously unbound). -/
theorem matchPat_var_spec {x : String} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.var (.base x)) t bnds0 = some bnds) :
    (bnds = bnds0 ∧ ∃ ty, bndLookup bnds0 x = some ty) ∨
    (bnds0.find? (fun b => b.1 == x) = none ∧ bnds = (x, t) :: bnds0) := by
  simp only [AST.matchPat] at hm
  cases hfx : bnds0.find? (fun b => b.1 == x) with
  | some pr =>
      obtain ⟨a, t'⟩ := pr
      rw [hfx] at hm
      simp only at hm
      split at hm
      · injection hm with hm
        refine Or.inl ⟨hm.symm, t', ?_⟩
        unfold bndLookup; rw [hfx]; rfl
      · simp at hm
  | none =>
      rw [hfx] at hm
      simp only at hm
      injection hm with hm
      exact Or.inr ⟨rfl, hm.symm⟩

/-! ### Shared matcher inversions

Three small inversions factor out the structural unfolding the three families below (monotonicity,
coverage, the substitution invariant) all repeat: a constructor-headed pattern forces the subject's head
and reduces to a list match, and a cons list match splits into a head match and a tail match. -/

/-- A successful constructor-headed match reduces to a successful list match against the same head. -/
theorem matchPat_sexp_inv {l : Label} {ps : List AST} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.sexp l ps) t bnds0 = some bnds) :
    ∃ ts, t = .sexp l ts ∧ AST.matchPatList ps ts bnds0 = some bnds := by
  obtain ⟨ts, rfl⟩ := matchPat_sexp_head hm
  simp only [AST.matchPat, beq_self_eq_true, if_true] at hm
  exact ⟨ts, rfl, hm⟩

/-- A cons list match against a known cons subject splits into a head match and a tail match. -/
theorem matchPatList_cons_eq {p : AST} {ps : List AST} {t' : AST} {ts'' : List AST}
    {bnds0 bnds : List (String × AST)} (hm : AST.matchPatList (p :: ps) (t' :: ts'') bnds0 = some bnds) :
    ∃ bnds1, AST.matchPat p t' bnds0 = some bnds1 ∧ AST.matchPatList ps ts'' bnds1 = some bnds := by
  simp only [AST.matchPatList] at hm
  rw [Option.bind_eq_some_iff] at hm
  exact hm

/-- A successful cons list match forces a cons subject and splits into a head and a tail match. -/
theorem matchPatList_cons_inv {p : AST} {ps ts : List AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPatList (p :: ps) ts bnds0 = some bnds) :
    ∃ t' ts'' bnds1, ts = t' :: ts'' ∧ AST.matchPat p t' bnds0 = some bnds1 ∧
      AST.matchPatList ps ts'' bnds1 = some bnds := by
  cases ts with
  | nil => simp [AST.matchPatList] at hm
  | cons t' ts'' =>
      obtain ⟨bnds1, h1, h2⟩ := matchPatList_cons_eq hm
      exact ⟨t', ts'', bnds1, rfl, h1, h2⟩

/-! ### Monotonicity: matching only extends the binding set

The matcher either leaves the bindings untouched (an already-bound variable that matches consistently)
or prepends a new one. Either way a binding once present is found unchanged afterwards. -/

mutual
  /-- Matching a well-sorted pattern preserves every existing binding. -/
  theorem matchPat_find_mono {p : Presentation} {Δ : Ctx} :
      ∀ {lhs : AST} {c : Cat}, WellSorted p Δ lhs c →
        ∀ {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
        ∀ {y : String} {v : String × AST}, bnds0.find? (fun b => b.1 == y) = some v →
          bnds.find? (fun b => b.1 == y) = some v
    | _, _, .var (x := x) hx, t, bnds0, bnds, hm, y, v, hf => by
        rcases matchPat_var_spec hm with ⟨rfl, _⟩ | ⟨hnone, rfl⟩
        · exact hf
        · rw [List.find?_cons]
          split
          · rename_i hxy
            have hxy' : x = y := eq_of_beq hxy
            subst hxy'
            rw [hnone] at hf; simp at hf
          · exact hf
    | _, _, .sexp r hmem hlabel hargs, t, bnds0, bnds, hm, y, v, hf => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        exact matchPatList_find_mono hargs hml hf
  /-- Matching a well-sorted argument list preserves every existing binding. -/
  theorem matchPatList_find_mono {p : Presentation} {Δ : Ctx} :
      ∀ {ps : List AST} {cs : List Cat}, WellSortedList p Δ ps cs →
        ∀ {ts : List AST} {bnds0 bnds : List (String × AST)},
          AST.matchPatList ps ts bnds0 = some bnds →
        ∀ {y : String} {v : String × AST}, bnds0.find? (fun b => b.1 == y) = some v →
          bnds.find? (fun b => b.1 == y) = some v
    | _, _, .nil, ts, bnds0, bnds, hm, y, v, hf => by
        cases ts with
        | nil => simp only [AST.matchPatList] at hm; injection hm with hm; subst hm; exact hf
        | cons t ts => simp [AST.matchPatList] at hm
    | _, _, .cons ha has, ts, bnds0, bnds, hm, y, v, hf => by
        obtain ⟨t', ts'', bnds1, rfl, h1, h2⟩ := matchPatList_cons_inv hm
        exact matchPatList_find_mono has h2 (matchPat_find_mono ha h1 hf)
end

/-- `bndLookup` version of monotonicity through a list match. -/
theorem bndLookup_mono {p : Presentation} {Δ : Ctx} {ps : List AST} {cs : List Cat}
    (hargs : WellSortedList p Δ ps cs) {ts : List AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPatList ps ts bnds0 = some bnds) {x : String} {ty : AST}
    (h : bndLookup bnds0 x = some ty) : bndLookup bnds x = some ty := by
  unfold bndLookup at h ⊢
  obtain ⟨pr, hpr, hpr2⟩ := Option.map_eq_some_iff.1 h
  rw [matchPatList_find_mono hargs hm hpr]
  exact Option.map_eq_some_iff.2 ⟨pr, rfl, hpr2⟩

/-- Matching a variable pattern binds that variable. -/
theorem matchPat_var_bound {x : String} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.var (.base x)) t bnds0 = some bnds) : ∃ ty, bndLookup bnds x = some ty := by
  rcases matchPat_var_spec hm with ⟨rfl, hty⟩ | ⟨_, rfl⟩
  · exact hty
  · exact ⟨t, bndLookup_cons_self x t bnds0⟩

/-! ### Coverage: matching binds every pattern variable -/

mutual
  /-- Every variable of a well-sorted pattern is bound after a successful match. -/
  theorem matchPat_cover {p : Presentation} {Δ : Ctx} :
      ∀ {lhs : AST} {c : Cat}, WellSorted p Δ lhs c →
        ∀ {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
        ∀ {x : String}, x ∈ varsOf lhs → ∃ ty, bndLookup bnds x = some ty
    | _, _, .var (x := x') hx, t, bnds0, bnds, hm, x, hx_mem => by
        simp only [varsOf, List.mem_singleton] at hx_mem
        subst hx_mem
        exact matchPat_var_bound hm
    | _, _, .sexp r hmem hlabel hargs, t, bnds0, bnds, hm, x, hx_mem => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        simp only [varsOf] at hx_mem
        exact matchPatList_cover hargs hml hx_mem
  /-- Every variable of a well-sorted argument list is bound after a successful list match. -/
  theorem matchPatList_cover {p : Presentation} {Δ : Ctx} :
      ∀ {ps : List AST} {cs : List Cat}, WellSortedList p Δ ps cs →
        ∀ {ts : List AST} {bnds0 bnds : List (String × AST)},
          AST.matchPatList ps ts bnds0 = some bnds →
        ∀ {x : String}, x ∈ varsOfList ps → ∃ ty, bndLookup bnds x = some ty
    | _, _, .nil, ts, bnds0, bnds, hm, x, hx_mem => by simp [varsOfList] at hx_mem
    | _, _, .cons ha has, ts, bnds0, bnds, hm, x, hx_mem => by
        obtain ⟨t', ts'', bnds1, rfl, h1, h2⟩ := matchPatList_cons_inv hm
        simp only [varsOfList, List.mem_append] at hx_mem
        rcases hx_mem with hxa | hxas
        · obtain ⟨ty, hty⟩ := matchPat_cover ha h1 hxa
          exact ⟨ty, bndLookup_mono has h2 hty⟩
        · exact matchPatList_cover has h2 hxas
end

/-! ### The well-sorted-substitution invariant

Matching a well-sorted subject against a well-sorted pattern keeps the bindings a well-sorted
substitution: each variable is bound to a term well-sorted at that variable's declared sort. -/

mutual
  /-- Matching against a well-sorted pattern preserves the well-sorted-substitution invariant. -/
  theorem matchPat_wssub {p : Presentation} {Γ Δ : Ctx} (hwf : LabelDeterminesRule p) :
      ∀ {lhs : AST} {c : Cat}, WellSorted p Δ lhs c →
        ∀ {t : AST} {bnds0 bnds : List (String × AST)}, WellSorted p Γ t c →
          AST.matchPat lhs t bnds0 = some bnds → WSsub p Γ Δ bnds0 → WSsub p Γ Δ bnds
    | _, _, .var (x := x') hx, t, bnds0, bnds, hwt, hm, hinv => by
        intro y ty cy hly hΔy
        rcases matchPat_var_spec hm with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · exact hinv y ty cy hly hΔy
        · by_cases hxy : x' = y
          · subst hxy
            rw [bndLookup_cons_self] at hly
            injection hly with hly
            rw [hx] at hΔy; injection hΔy with hcy
            rw [← hly, ← hcy]; exact hwt
          · rw [bndLookup_cons_of_ne hxy] at hly
            exact hinv y ty cy hly hΔy
    | _, _, .sexp r hmem hlabel hargs, t, bnds0, bnds, hwt, hm, hinv => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        obtain ⟨r', hmem', hlabel', _, hargs'⟩ := wellSorted_sexp_inv hwt
        have hsorts : r.argSorts = r'.argSorts := hwf r hmem r' hmem' (by rw [hlabel, hlabel'])
        rw [← hsorts] at hargs'
        exact matchPatList_wssub hwf hargs hargs' hml hinv
  /-- Matching an argument list against a well-sorted pattern list preserves the invariant. -/
  theorem matchPatList_wssub {p : Presentation} {Γ Δ : Ctx} (hwf : LabelDeterminesRule p) :
      ∀ {ps : List AST} {cs : List Cat}, WellSortedList p Δ ps cs →
        ∀ {ts : List AST} {bnds0 bnds : List (String × AST)}, WellSortedList p Γ ts cs →
          AST.matchPatList ps ts bnds0 = some bnds → WSsub p Γ Δ bnds0 → WSsub p Γ Δ bnds
    | _, _, .nil, ts, bnds0, bnds, hwt, hm, hinv => by
        have hts := wellSortedList_nil_inv hwt; subst hts
        simp only [AST.matchPatList] at hm; injection hm with hm; subst hm; exact hinv
    | _, _, .cons ha has, ts, bnds0, bnds, hwt, hm, hinv => by
        obtain ⟨t', ts'', rfl, ht', hts''⟩ := wellSortedList_cons_sort_inv hwt
        obtain ⟨bnds1, h1, h2⟩ := matchPatList_cons_eq hm
        exact matchPatList_wssub hwf has hts'' h2 (matchPat_wssub hwf ha ht' h1 hinv)
end

/-! ### Subject reduction for a base rewrite

The two halves combine: matching gives a well-sorted substitution (`matchPat_wssub`) that covers every
pattern variable (`matchPat_cover`), and instantiation preserves well-sortedness (`inst_wellSorted`). So a
base rewrite whose two sides are well-sorted under a shared context, applied to a well-sorted subject,
yields a well-sorted result at the same sort. -/

theorem subjectReduction_base {p : Presentation} {Γ Δ : Ctx} (hwf : LabelDeterminesRule p)
    {lhs rhs t : AST} {c : Cat} {bnds : List (String × AST)}
    (hlhs : WellSorted p Δ lhs c) (hrhs : WellSorted p Δ rhs c)
    (hcov : ∀ x cx, Δ.lookup x = some cx → x ∈ varsOf lhs)
    (hsub : WellSorted p Γ t c) (hmatch : AST.matchPat lhs t [] = some bnds) :
    WellSorted p Γ (AST.inst bnds rhs) c := by
  have hwssub : WSsub p Γ Δ bnds :=
    matchPat_wssub hwf hlhs hsub hmatch (by intro y ty cy hly _; simp [bndLookup] at hly)
  have hb : ∀ x cx, Δ.lookup x = some cx → WellSorted p Γ (AST.inst bnds (.var (.base x))) cx := by
    intro x cx hΔx
    obtain ⟨ty, hty⟩ := matchPat_cover hlhs hmatch (hcov x cx hΔx)
    rw [inst_var_of_bndLookup hty]
    exact hwssub x ty cx hty hΔx
  exact inst_wellSorted hb hrhs

/-! ### Lifting through the reduction relation

Subject reduction lifts from base contractions to the runtime's full one-step `RewStep` and many-step
`RewStepMany`. The congruence case (a step inside an argument) holds because the argument keeps its sort,
and the `Subst` cases are vacuous: a well-sorted term has no `Subst` node. The top-level hypothesis is
exactly base-contraction preservation, supplied by `subjectReduction_base` for well-sorted rules. -/

/-- One-step subject reduction: if base reductions preserve sorts, so does the context-closed `RewStep`. -/
theorem rewStep_preserves_wellSorted {p : Presentation} {Γ : Ctx}
    (htop : ∀ t t' c, Reduces p t t' → WellSorted p Γ t c → WellSorted p Γ t' c)
    {t t' : AST} (hstep : RewStep p t t') :
    ∀ {c : Cat}, WellSorted p Γ t c → WellSorted p Γ t' c := by
  induction hstep with
  | top hred => intro c hws; exact htop _ _ c hred hws
  | @arg l pre post a a' ha ih =>
      intro c hws
      obtain ⟨r, hmem, hlabel, hcat, hargs⟩ := wellSorted_sexp_inv hws
      subst hcat
      exact .sexp r hmem hlabel (wellSortedList_arg_subst (fun _ hwa => ih hwa) hargs)
  | substB _ _ => intro c hws; cases hws
  | substR _ _ => intro c hws; cases hws

/-- Many-step subject reduction: sorts are preserved along any reduction sequence. -/
theorem rewStepMany_preserves_wellSorted {p : Presentation} {Γ : Ctx}
    (htop : ∀ t t' c, Reduces p t t' → WellSorted p Γ t c → WellSorted p Γ t' c)
    {t t' : AST} (hsteps : RewStepMany p t t') {c : Cat} :
    WellSorted p Γ t c → WellSorted p Γ t' c := by
  induction hsteps with
  | refl => exact id
  | tail _ s ih => exact fun hws => rewStep_preserves_wellSorted htop s (ih hws)

/-! ## A worked instance: recursive subject reduction with a variable rule

`srPres` declares a sort `T`, a constant `a`, and two unary symbols `f`, `g`, with the rewrite
`(f x) ~> (g x)` carrying a real pattern variable `x : T`. Reducing the ground term `(f a)` binds
`x` to `a` and produces `(g a)`; `subjectReduction_sr` is the machine-checked statement that the result
is well-sorted at `T`, obtained from `subjectReduction_base` (so every subterm keeps its declared sort
across the variable-instantiating step). -/

private def srT : Cat := .idCat "T"
private def srRule (n : String) (items : List Item) : Rule :=
  { label := .id n, cat := srT, items := items }

/-- A presentation with a constant, two unary symbols, and a variable-carrying rewrite. -/
def srPres : Presentation :=
  .mk [srT] [srRule "a" [], srRule "f" [.nterminal srT], srRule "g" [.nterminal srT]] []
    [ { name := "r",
        rw := .base (.sexp (.id "f") [.var (.base "x")]) (.sexp (.id "g") [.var (.base "x")]) } ] []

theorem srPres_wf : LabelDeterminesRule srPres := by
  intro r1 hr1 r2 hr2 hlab
  simp only [srPres] at hr1 hr2
  fin_cases hr1 <;> fin_cases hr2 <;> simp_all [srRule]

/-- The pattern `(f x)` is well-sorted at `T` in the context `x : T`. -/
theorem srLhs_ws : WellSorted srPres [("x", srT)] (.sexp (.id "f") [.var (.base "x")]) srT :=
  .sexp (srRule "f" [.nterminal srT]) (by decide) rfl
    (.cons (.var (by decide)) .nil)

/-- The contractum `(g x)` is well-sorted at `T` in the same context. -/
theorem srRhs_ws : WellSorted srPres [("x", srT)] (.sexp (.id "g") [.var (.base "x")]) srT :=
  .sexp (srRule "g" [.nterminal srT]) (by decide) rfl
    (.cons (.var (by decide)) .nil)

/-- The subject `(f a)` is well-sorted at `T` in the empty context (it is ground). -/
theorem srSubj_ws : WellSorted srPres [] (.sexp (.id "f") [.sexp (.id "a") []]) srT :=
  .sexp (srRule "f" [.nterminal srT]) (by decide) rfl
    (.cons (.sexp (srRule "a" []) (by decide) rfl .nil) .nil)

/-- The rule's context is covered by the variables of its left-hand side. -/
theorem srCov : ∀ x cx, ([("x", srT)] : Ctx).lookup x = some cx →
    x ∈ varsOf (.sexp (.id "f") [.var (.base "x")]) := by
  intro y cy h
  simp only [List.lookup] at h
  split at h
  · rename_i hyx
    have : y = "x" := eq_of_beq hyx
    subst this
    simp [varsOf, varsOfList]
  · simp at h

/-- Matching the subject against the pattern binds `x` to `a`. -/
theorem srMatch : AST.matchPat (.sexp (.id "f") [.var (.base "x")])
    (.sexp (.id "f") [.sexp (.id "a") []]) [] = some [("x", .sexp (.id "a") [])] := by decide

/-- Subject reduction on the concrete step `(f a) ~> (g a)`: the result is well-sorted at `T`. -/
theorem subjectReduction_sr :
    WellSorted srPres [] (AST.inst [("x", .sexp (.id "a") [])] (.sexp (.id "g") [.var (.base "x")])) srT :=
  subjectReduction_base srPres_wf srLhs_ws srRhs_ws srCov srSubj_ws srMatch

/-- And the instantiated contractum is concretely `(g a)`. -/
theorem srResult : AST.inst [("x", .sexp (.id "a") [])] (.sexp (.id "g") [.var (.base "x")])
    = .sexp (.id "g") [.sexp (.id "a") []] := by decide

end MeTTaIL
