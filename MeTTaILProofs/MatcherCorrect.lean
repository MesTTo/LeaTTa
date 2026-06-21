/-
Module: MeTTaILProofs.MatcherCorrect
Layer: Proofs
Purpose: Correctness of the runtime matcher: a successful match produces a substitution that reconstructs
  the matched term. The headline `matchPat_inst_eq` proves `matchPat lhs t [] = some bnds → inst bnds lhs = t`
  for the rewriting fragment (subst-free patterns). This certifies that the reduction relation only encodes
  genuine rule applications: a base step `t ~> inst bnds rhs` really does fire `lhs ~> rhs` at a substitution
  with `t = inst bnds lhs`. The repeated-variable case is exactly the re-check that MORK's Verus proofs
  validate (`BindingEnv`: re-binding the same value is a no-op, a conflict is rejected; `VarRefRecheck`: the
  equality re-check of an already-bound variable is sound), here justified by the matcher's consistency test
  `t' == t`. Supporting: matcher monotonicity (matching only extends the bindings), coverage (every pattern
  variable ends up bound), and `inst_agree` (instantiation depends only on the pattern's variables).
Imports: MeTTaILProofs.SubjectReduction (varsOf, bndLookup, the matcher inversions), MeTTaILProofs.DecEq
Trusted boundary: none (fully proved)
Main exports: SubstFree, inst_agree, matchPat_mono_sf, matchPat_cover_sf, matchPat_inst_eq
Open obligations: the `Subst`/binder fragment (where `inst` resolves a substitution rather than matching
  structurally) is out of scope, as for the rest of the first-order layer.
-/
import MeTTaILProofs.SubjectReduction
import MeTTaILProofs.DecEq

namespace MeTTaIL

mutual
  /-- A term of the rewriting fragment: no `Subst` node anywhere. Rule sides live here. -/
  def SubstFree : AST → Prop
    | .var _ => True
    | .sexp _ args => SubstFreeList args
    | .subst _ _ _ => False
  def SubstFreeList : List AST → Prop
    | [] => True
    | a :: as => SubstFree a ∧ SubstFreeList as
end

mutual
  /-- Well-sorted terms are subst-free. The sort discipline (`WellSorted` has only `var` and `sexp` cases,
      no `Subst` rule) rejects every `Subst` node, so a `Subst` term is never well-sorted. Hence the
      subst-free fragment on which matcher correctness and the critical-pair confluence are stated coincides
      with the well-sorted-TERM fragment.

      Scope, stated honestly: this does NOT by itself cover rules whose right-hand side is a `Subst` (for
      example the rho-calculus COMM rule in `MeTTaILTests/Rholang.lean`, whose RHS is `.subst ...`). Such a
      rule's RHS is not well-sorted as written, and its reduct becomes subst-free only after `inst` resolves
      the `Subst`. Subject reduction THROUGH that explicit-substitution resolution is a separate obligation
      (the binder fragment), not discharged by this lemma. So this closes the first-order rewriting fragment,
      not the binder fragment. -/
  theorem wellSorted_substFree {p : Presentation} {Γ : Ctx} :
      ∀ {t : AST} {c : Cat}, WellSorted p Γ t c → SubstFree t
    | _, _, .var _ => trivial
    | _, _, .sexp _ _ _ hargs => wellSortedList_substFree hargs
  theorem wellSortedList_substFree {p : Presentation} {Γ : Ctx} :
      ∀ {ts : List AST} {cs : List Cat}, WellSortedList p Γ ts cs → SubstFreeList ts
    | _, _, .nil => trivial
    | _, _, .cons ha has => ⟨wellSorted_substFree ha, wellSortedList_substFree has⟩
end

mutual
  /-- Structural instantiation: like `AST.inst` but it does NOT resolve a `Subst` node, rebuilding it
      structurally with its bound variable kept literally. This is exactly the reconstruction the matcher
      inverts: the matcher is purely structural and matches a `Subst` pattern's bound variable by syntactic
      equality, so matcher correctness is stated against `instStruct` for the FULL pattern language. On the
      subst-free fragment `instStruct` agrees with `inst` (`instStruct_eq_inst_substFree`), so the `inst`
      theorems are recovered as corollaries. -/
  def AST.instStruct (bnds : List (String × AST)) : AST → AST
    | .var (.base v) =>
        match bnds.find? (fun b => b.1 == v) with
        | some (_, t) => t
        | none => .var (.base v)
    | .var p => .var p
    | .sexp l args => .sexp l (AST.instStructList bnds args)
    | .subst b r w => .subst (AST.instStruct bnds b) (AST.instStruct bnds r) w
  /-- Structural instantiation through an argument list. -/
  def AST.instStructList (bnds : List (String × AST)) : List AST → List AST
    | [] => []
    | a :: as => AST.instStruct bnds a :: AST.instStructList bnds as
end

mutual
  /-- On the subst-free fragment, structural instantiation and `inst` coincide (they differ only on `Subst`
      nodes, of which a subst-free term has none). -/
  theorem instStruct_eq_inst_substFree {bnds : List (String × AST)} :
      ∀ {t : AST}, SubstFree t → AST.instStruct bnds t = AST.inst bnds t
    | .var (.base _), _ => rfl
    | .var (.qualified _ _), _ => rfl
    | .sexp l args, hsf => by
        simp only [AST.instStruct, AST.inst]
        rw [instStructList_eq_instList_substFree (by simpa [SubstFree] using hsf)]
  theorem instStructList_eq_instList_substFree {bnds : List (String × AST)} :
      ∀ {ts : List AST}, SubstFreeList ts → AST.instStructList bnds ts = AST.instList bnds ts
    | [], _ => rfl
    | a :: as, ⟨h, hs⟩ => by
        simp only [AST.instStructList, AST.instList]
        rw [instStruct_eq_inst_substFree h, instStructList_eq_instList_substFree hs]
end

/-- Extend a typing context along a path: a base name `y` binds `y : c`; a qualified path binds nothing
    (no well-sorted variable can equal a qualified path), so the context is unchanged. -/
def Ctx.extendPath (Γ : Ctx) (q : DottedPath) (c : Cat) : Ctx :=
  match q with
  | .base y => (y, c) :: Γ
  | _ => Γ

mutual
  /-- The substitution lemma along an arbitrary path (the general `subst1` half), the binder-fragment
      counterpart of `inst_wellSorted`: substituting a term well-sorted at `c` for the path `q` in a term
      well-sorted at `d` in the path-extended context yields a term well-sorted at `d`. For `q = .base y`
      this is the binder substitution lemma; for a qualified path it holds vacuously (no well-sorted
      variable matches a qualified path, so the term is unchanged and the extended context is `Γ`). This is
      the key lemma for subject reduction of rules whose right-hand side is a `Subst` (explicit
      substitution), such as the rho-calculus COMM rule (`MeTTaILTests/Rholang.lean`), whose reduct is
      `inst`-resolved through `subst1`, INCLUDING the captured-bound-variable (alpha) case where the match
      remaps the bound variable to another runtime variable. Kept here rather than in `Semantics` because it
      needs `LawfulBEq DottedPath` from `DecEq`. -/
  theorem subst1_wellSorted_path {p : Presentation} {Γ : Ctx} {q : DottedPath} {c : Cat} {repl : AST}
      (hr : WellSorted p Γ repl c) :
      ∀ {t : AST} {d : Cat}, WellSorted p (Γ.extendPath q c) t d →
        WellSorted p Γ (AST.subst1 q repl t) d
    | _, _, .var (x := x) hx => by
        cases q with
        | base y =>
            simp only [Ctx.extendPath] at hx
            rw [List.lookup_cons] at hx
            split at hx
            · rename_i hyx
              obtain rfl := beq_iff_eq.mp hyx
              simp only [Option.some.injEq] at hx; subst hx
              simpa [AST.subst1] using hr
            · rename_i hyx
              simp only [AST.subst1]
              split
              · rename_i hbe
                rw [(by simpa only [beq_iff_eq, DottedPath.base.injEq] using hbe : x = y)] at hyx
                simp at hyx
              · exact WellSorted.var hx
        | qualified i r =>
            simp only [Ctx.extendPath] at hx
            have hne : AST.subst1 (.qualified i r) repl (.var (.base x)) = .var (.base x) := by
              simp [AST.subst1]
            rw [hne]; exact WellSorted.var hx
    | _, _, .sexp r hmem hlabel hargs =>
        WellSorted.sexp r hmem hlabel (subst1List_wellSorted_path hr hargs)
  theorem subst1List_wellSorted_path {p : Presentation} {Γ : Ctx} {q : DottedPath} {c : Cat} {repl : AST}
      (hr : WellSorted p Γ repl c) :
      ∀ {ts : List AST} {cs : List Cat}, WellSortedList p (Γ.extendPath q c) ts cs →
        WellSortedList p Γ (AST.subst1List q repl ts) cs
    | _, _, .nil => WellSortedList.nil
    | _, _, .cons ha has =>
        WellSortedList.cons (subst1_wellSorted_path hr ha) (subst1List_wellSorted_path hr has)
end

/-- The binder substitution lemma for a base variable `y`: the `q = .base y` instance of
    `subst1_wellSorted_path` (the original first-order/binder substitution lemma). -/
theorem subst1_wellSorted {p : Presentation} {Γ : Ctx} {y : String} {c : Cat} {repl : AST}
    (hr : WellSorted p Γ repl c) {t : AST} {d : Cat} (ht : WellSorted p ((y, c) :: Γ) t d) :
    WellSorted p Γ (AST.subst1 (.base y) repl t) d :=
  subst1_wellSorted_path hr (q := .base y) ht

/-- The substitution target that `AST.inst` computes for a `Subst` node's bound variable `w`: a base name
    bound by the match to a runtime variable `.var p` is remapped to `p` (the capture-avoiding rename);
    otherwise `w` itself. Mirrors the `let w' := ...` inside `AST.inst`'s `.subst` case. -/
def AST.instSubstTarget (bnds : List (String × AST)) : DottedPath → DottedPath
  | .base name =>
      match bnds.find? (fun b => b.1 == name) with
      | some (_, .var p) => p
      | _ => .base name
  | q => q

/-- `AST.inst` on a `Subst` node resolves it to a `subst1` along the remapped target. -/
theorem inst_subst_eq (bnds : List (String × AST)) (b r : AST) (w : DottedPath) :
    AST.inst bnds (.subst b r w)
      = AST.subst1 (AST.instSubstTarget bnds w) (AST.inst bnds r) (AST.inst bnds b) := by
  cases w with
  | base name =>
      simp only [AST.inst, AST.instSubstTarget]
      cases bnds.find? (fun b => b.1 == name) with
      | none => rfl
      | some pr => obtain ⟨a, t⟩ := pr; cases t <;> rfl
  | qualified i r => rfl

/-- Subject reduction for a `Subst` right-hand side (the binder fragment), in FULL generality including the
    captured-bound-variable (alpha) case: the `inst`-resolved reduct of a rule whose RHS is `subst b r w` is
    well-sorted. `inst` resolves the explicit substitution to a `subst1` along the remapped target
    `instSubstTarget bnds w` (the bound variable `w`, or the runtime variable it was matched to), so the
    reduct is well-sorted when the instantiated body `inst bnds b` is well-sorted at `d` in the context
    extended by that target and the instantiated `inst bnds r` is well-sorted at the target's sort. This
    covers the rho-calculus COMM rule's reduction, INCLUDING when its bound variable is captured/remapped by
    the match (the alpha case the earlier freshness-restricted version excluded). -/
theorem reduces_subst_wellSorted {p : Presentation} {Γ : Ctx} {bnds : List (String × AST)}
    {b r : AST} {w : DottedPath} {d cw : Cat}
    (hb : WellSorted p (Γ.extendPath (AST.instSubstTarget bnds w) cw) (AST.inst bnds b) d)
    (hr : WellSorted p Γ (AST.inst bnds r) cw) :
    WellSorted p Γ (AST.inst bnds (.subst b r w)) d := by
  rw [inst_subst_eq]
  exact subst1_wellSorted_path hr hb

/-- If a variable is unbound, instantiation leaves it alone. -/
theorem inst_var_none {bnds : List (String × AST)} {v : String} (h : bndLookup bnds v = none) :
    AST.inst bnds (.var (.base v)) = .var (.base v) := by
  unfold bndLookup at h
  rw [Option.map_eq_none_iff] at h
  unfold AST.inst
  rw [h]

/-! ### Instantiation depends only on the pattern's variables -/

mutual
  /-- Two substitutions agreeing on a (subst-free) term's variables instantiate it the same way. -/
  theorem inst_agree {bnds1 bnds2 : List (String × AST)} :
      ∀ {lhs : AST}, SubstFree lhs → (∀ v ∈ varsOf lhs, bndLookup bnds1 v = bndLookup bnds2 v) →
        AST.inst bnds1 lhs = AST.inst bnds2 lhs
    | .var (.base v), _, h => by
        have hv := h v (by simp [varsOf])
        cases hb : bndLookup bnds1 v with
        | some ty => rw [inst_var_of_bndLookup hb, inst_var_of_bndLookup (hv ▸ hb)]
        | none => rw [inst_var_none hb, inst_var_none (hv ▸ hb)]
    | .var (.qualified _ _), _, _ => rfl
    | .sexp l args, hsf, h => by
        simp only [AST.inst]
        congr 1
        exact instList_agree (by simpa [SubstFree] using hsf) (by simpa [varsOf] using h)
  /-- The argument-list version. -/
  theorem instList_agree {bnds1 bnds2 : List (String × AST)} :
      ∀ {args : List AST}, SubstFreeList args →
        (∀ v ∈ varsOfList args, bndLookup bnds1 v = bndLookup bnds2 v) →
        AST.instList bnds1 args = AST.instList bnds2 args
    | [], _, _ => rfl
    | a :: as, hsf, h => by
        simp only [AST.instList]
        simp only [SubstFreeList] at hsf
        simp only [varsOfList] at h
        rw [inst_agree hsf.1 (fun v hv => h v (by simp [hv])),
          instList_agree hsf.2 (fun v hv => h v (by simp [hv]))]
end

/-- `instStruct` on a bound base variable returns its binding (defeq to the `inst` version). -/
theorem instStruct_var_of_bndLookup {bnds : List (String × AST)} {v : String} {ty : AST}
    (h : bndLookup bnds v = some ty) : AST.instStruct bnds (.var (.base v)) = ty :=
  inst_var_of_bndLookup h

/-- `instStruct` leaves an unbound base variable alone (defeq to the `inst` version). -/
theorem instStruct_var_none {bnds : List (String × AST)} {v : String}
    (h : bndLookup bnds v = none) : AST.instStruct bnds (.var (.base v)) = .var (.base v) :=
  inst_var_none h

/-- `instStruct` and `inst` coincide on a base variable (they have identical defining clauses there). -/
theorem instStruct_var_eq_inst {bnds : List (String × AST)} {v : String} :
    AST.instStruct bnds (.var (.base v)) = AST.inst bnds (.var (.base v)) := rfl

mutual
  /-- Two substitutions agreeing on a term's variables instantiate it the same way, for the FULL language
      (the `instStruct` counterpart of `inst_agree`, with no subst-free restriction). -/
  theorem instStruct_agree {bnds1 bnds2 : List (String × AST)} :
      ∀ {t : AST}, (∀ v ∈ varsOf t, bndLookup bnds1 v = bndLookup bnds2 v) →
        AST.instStruct bnds1 t = AST.instStruct bnds2 t
    | .var (.base v), h => by
        have hv := h v (by simp [varsOf])
        cases hb : bndLookup bnds1 v with
        | some ty => rw [instStruct_var_of_bndLookup hb, instStruct_var_of_bndLookup (hv ▸ hb)]
        | none => rw [instStruct_var_none hb, instStruct_var_none (hv ▸ hb)]
    | .var (.qualified _ _), _ => rfl
    | .sexp l args, h => by
        simp only [AST.instStruct]
        congr 1
        exact instStructList_agree (by simpa [varsOf] using h)
    | .subst b r w, h => by
        simp only [AST.instStruct]
        rw [instStruct_agree (fun v hv => h v (by simp [varsOf, hv])),
          instStruct_agree (fun v hv => h v (by simp [varsOf, hv]))]
  /-- The argument-list version. -/
  theorem instStructList_agree {bnds1 bnds2 : List (String × AST)} :
      ∀ {args : List AST}, (∀ v ∈ varsOfList args, bndLookup bnds1 v = bndLookup bnds2 v) →
        AST.instStructList bnds1 args = AST.instStructList bnds2 args
    | [], _ => rfl
    | a :: as, h => by
        simp only [AST.instStructList]
        rw [instStruct_agree (fun v hv => h v (by simp [varsOfList, hv])),
          instStructList_agree (fun v hv => h v (by simp [varsOfList, hv]))]
end

/-- A successful `Subst`-headed match forces a `Subst` subject with the same (syntactic) bound variable, and
    splits into a match of the body and a match of the replacement. -/
theorem matchPat_subst_inv {pb pr : AST} {pv : DottedPath} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.subst pb pr pv) t bnds0 = some bnds) :
    ∃ tb tr, t = .subst tb tr pv ∧ ∃ bnds1, AST.matchPat pb tb bnds0 = some bnds1 ∧
      AST.matchPat pr tr bnds1 = some bnds := by
  cases t with
  | var p => simp [AST.matchPat] at hm
  | sexp l ts => simp [AST.matchPat] at hm
  | subst tb tr tv =>
      simp only [AST.matchPat] at hm
      split at hm
      · rename_i hpv
        obtain rfl : pv = tv := eq_of_beq hpv
        rw [Option.bind_eq_some_iff] at hm
        obtain ⟨bnds1, h1, h2⟩ := hm
        exact ⟨tb, tr, rfl, bnds1, h1, h2⟩
      · simp at hm

/-! ### Matching a variable reconstructs the matched term -/

/-- A successful match of a qualified-path variable forces the term to be that variable and leaves the
    bindings unchanged (it is a structural-equality match). -/
theorem matchPat_qual {i : String} {r : DottedPath} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.var (.qualified i r)) t bnds0 = some bnds) :
    bnds = bnds0 ∧ t = .var (.qualified i r) := by
  simp only [AST.matchPat] at hm
  split at hm
  · rename_i he; injection hm with hm; exact ⟨hm.symm, (eq_of_beq he).symm⟩
  · simp at hm

/-- Matching a base variable binds it to the matched term: instantiation gives the term back. The
    repeated-variable case uses the matcher's consistency test `t' == t`, the equality re-check that MORK's
    `VarRefRecheck`/`BindingEnv` Verus proofs validate. -/
theorem matchPat_var_inst {x : String} {t : AST} {bnds0 bnds : List (String × AST)}
    (hm : AST.matchPat (.var (.base x)) t bnds0 = some bnds) : AST.inst bnds (.var (.base x)) = t := by
  simp only [AST.matchPat] at hm
  cases hfx : bnds0.find? (fun b => b.1 == x) with
  | some pr =>
      obtain ⟨a, t'⟩ := pr
      rw [hfx] at hm; simp only at hm
      split at hm
      · rename_i ht'; injection hm with hm; subst hm
        rw [inst_var_of_bndLookup (show bndLookup bnds0 x = some t' from by
          unfold bndLookup; rw [hfx]; rfl)]
        exact eq_of_beq ht'
      · simp at hm
  | none =>
      rw [hfx] at hm; simp only at hm; injection hm with hm; subst hm
      rw [inst_var_of_bndLookup (bndLookup_cons_self x t bnds0)]

/-! ### Matching only extends the bindings, and binds every pattern variable

`BindingEnv` in MORK's Verus proofs: a re-match is a no-op and a fresh bind only adds. -/

mutual
  /-- Matching ANY pattern preserves every existing binding (monotonicity, unconditional: the matcher only
      ever adds bindings, including through a `Subst` pattern's two sub-matches). -/
  theorem matchPat_mono_all :
      ∀ {lhs : AST} {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
      ∀ {v : String} {ty : AST}, bndLookup bnds0 v = some ty → bndLookup bnds v = some ty
    | .var (.base x), t, bnds0, bnds, hm, v, ty, hbl => by
        rcases matchPat_var_spec hm with ⟨rfl, _⟩ | ⟨hnone, rfl⟩
        · exact hbl
        · by_cases hxv : x = v
          · subst hxv; simp [bndLookup, hnone] at hbl
          · rw [bndLookup_cons_of_ne hxv]; exact hbl
    | .var (.qualified _ _), t, bnds0, bnds, hm, v, ty, hbl => by
        rw [(matchPat_qual hm).1]; exact hbl
    | .sexp l args, t, bnds0, bnds, hm, v, ty, hbl => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        exact matchPatList_mono_all hml hbl
    | .subst pb pr pv, t, bnds0, bnds, hm, v, ty, hbl => by
        obtain ⟨tb, tr, rfl, bnds1, h1, h2⟩ := matchPat_subst_inv hm
        exact matchPat_mono_all h2 (matchPat_mono_all h1 hbl)
  /-- The argument-list version. -/
  theorem matchPatList_mono_all :
      ∀ {ps : List AST} {ts : List AST} {bnds0 bnds : List (String × AST)},
        AST.matchPatList ps ts bnds0 = some bnds →
      ∀ {v : String} {ty : AST}, bndLookup bnds0 v = some ty → bndLookup bnds v = some ty
    | [], ts, bnds0, bnds, hm, v, ty, hbl => by
        cases ts with
        | nil => simp only [AST.matchPatList] at hm; injection hm with hm; subst hm; exact hbl
        | cons _ _ => simp [AST.matchPatList] at hm
    | a :: as, ts, bnds0, bnds, hm, v, ty, hbl => by
        obtain ⟨t1, ts'', bnds1, rfl, h1, h2⟩ := matchPatList_cons_inv hm
        exact matchPatList_mono_all h2 (matchPat_mono_all h1 hbl)
end

/-- Subst-free corollary of `matchPat_mono_all` (the original `matchPat_mono`). -/
theorem matchPat_mono : ∀ {lhs : AST}, SubstFree lhs →
    ∀ {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
    ∀ {v : String} {ty : AST}, bndLookup bnds0 v = some ty → bndLookup bnds v = some ty :=
  fun _ => matchPat_mono_all
/-- Subst-free corollary of `matchPatList_mono_all` (the original `matchPatList_mono`). -/
theorem matchPatList_mono : ∀ {ps : List AST}, SubstFreeList ps →
    ∀ {ts : List AST} {bnds0 bnds : List (String × AST)}, AST.matchPatList ps ts bnds0 = some bnds →
    ∀ {v : String} {ty : AST}, bndLookup bnds0 v = some ty → bndLookup bnds v = some ty :=
  fun _ => matchPatList_mono_all

mutual
  /-- Every variable of ANY pattern is bound after a successful match (coverage, unconditional, including a
      `Subst` pattern whose variables come from its body and replacement). -/
  theorem matchPat_cover_all :
      ∀ {lhs : AST} {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
      ∀ {v : String}, v ∈ varsOf lhs → ∃ ty, bndLookup bnds v = some ty
    | .var (.base x), t, bnds0, bnds, hm, v, hv => by
        simp only [varsOf, List.mem_singleton] at hv; subst hv
        exact matchPat_var_bound hm
    | .var (.qualified _ _), t, bnds0, bnds, hm, v, hv => by simp [varsOf] at hv
    | .sexp l args, t, bnds0, bnds, hm, v, hv => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        simp only [varsOf] at hv
        exact matchPatList_cover_all hml hv
    | .subst pb pr pv, t, bnds0, bnds, hm, v, hv => by
        obtain ⟨tb, tr, rfl, bnds1, h1, h2⟩ := matchPat_subst_inv hm
        simp only [varsOf, List.mem_append] at hv
        rcases hv with hvb | hvr
        · obtain ⟨ty, hty⟩ := matchPat_cover_all h1 hvb
          exact ⟨ty, matchPat_mono_all h2 hty⟩
        · exact matchPat_cover_all h2 hvr
  /-- The argument-list version. -/
  theorem matchPatList_cover_all :
      ∀ {ps : List AST} {ts : List AST} {bnds0 bnds : List (String × AST)},
        AST.matchPatList ps ts bnds0 = some bnds →
      ∀ {v : String}, v ∈ varsOfList ps → ∃ ty, bndLookup bnds v = some ty
    | [], ts, bnds0, bnds, hm, v, hv => by simp [varsOfList] at hv
    | a :: as, ts, bnds0, bnds, hm, v, hv => by
        obtain ⟨t1, ts'', bnds1, rfl, h1, h2⟩ := matchPatList_cons_inv hm
        simp only [varsOfList, List.mem_append] at hv
        rcases hv with hva | hvas
        · obtain ⟨ty, hty⟩ := matchPat_cover_all h1 hva
          exact ⟨ty, matchPatList_mono_all h2 hty⟩
        · exact matchPatList_cover_all h2 hvas
end

/-- Subst-free corollary of `matchPat_cover_all` (the original `matchPat_cover_sf`). -/
theorem matchPat_cover_sf : ∀ {lhs : AST}, SubstFree lhs →
    ∀ {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
    ∀ {v : String}, v ∈ varsOf lhs → ∃ ty, bndLookup bnds v = some ty :=
  fun _ => matchPat_cover_all
/-- Subst-free corollary of `matchPatList_cover_all` (the original `matchPatList_cover_sf`). -/
theorem matchPatList_cover_sf : ∀ {ps : List AST}, SubstFreeList ps →
    ∀ {ts : List AST} {bnds0 bnds : List (String × AST)}, AST.matchPatList ps ts bnds0 = some bnds →
    ∀ {v : String}, v ∈ varsOfList ps → ∃ ty, bndLookup bnds v = some ty :=
  fun _ => matchPatList_cover_all

/-! ### Matcher correctness: a successful match reconstructs the matched term -/

mutual
  /-- A successful match produces a substitution that STRUCTURALLY instantiates the pattern back to the
      matched term, for the FULL pattern language including `Subst` (the matcher inverts `instStruct`). -/
  theorem matchPat_instStruct_eq :
      ∀ {lhs : AST} {t : AST} {bnds0 bnds : List (String × AST)}, AST.matchPat lhs t bnds0 = some bnds →
        AST.instStruct bnds lhs = t
    | .var (.base _), _, _, _, hm => matchPat_var_inst hm
    | .var (.qualified i r), t, bnds0, bnds, hm => by
        obtain ⟨_, rfl⟩ := matchPat_qual hm; rfl
    | .sexp l args, t, bnds0, bnds, hm => by
        obtain ⟨ts, rfl, hml⟩ := matchPat_sexp_inv hm
        simp only [AST.instStruct]
        congr 1
        exact matchPatList_instStruct_eq hml
    | .subst pb pr pv, t, bnds0, bnds, hm => by
        obtain ⟨tb, tr, rfl, bnds1, h1, h2⟩ := matchPat_subst_inv hm
        simp only [AST.instStruct]
        have e1 : AST.instStruct bnds pb = tb := by
          rw [← matchPat_instStruct_eq h1]
          refine instStruct_agree (fun v hv => ?_)
          obtain ⟨ty, hty⟩ := matchPat_cover_all h1 hv
          rw [hty, matchPat_mono_all h2 hty]
        rw [e1, matchPat_instStruct_eq h2]
  /-- The argument-list version. -/
  theorem matchPatList_instStruct_eq :
      ∀ {ps : List AST} {ts : List AST} {bnds0 bnds : List (String × AST)},
        AST.matchPatList ps ts bnds0 = some bnds → AST.instStructList bnds ps = ts
    | [], ts, bnds0, bnds, hm => by
        cases ts with
        | nil => rfl
        | cons _ _ => simp [AST.matchPatList] at hm
    | a :: as, ts, bnds0, bnds, hm => by
        obtain ⟨t1, ts'', bnds1, rfl, h1, h2⟩ := matchPatList_cons_inv hm
        simp only [AST.instStructList]
        have htl : AST.instStructList bnds as = ts'' := matchPatList_instStruct_eq h2
        have hhd : AST.instStruct bnds a = t1 := by
          rw [← matchPat_instStruct_eq h1]
          refine instStruct_agree (fun v hv => ?_)
          obtain ⟨ty, hty⟩ := matchPat_cover_all h1 hv
          rw [hty, matchPatList_mono_all h2 hty]
        rw [hhd, htl]
end

/-- Subst-free corollary: a successful match `inst`-reconstructs the term (the original `matchPat_inst_eq`).
    On the subst-free fragment `inst = instStruct`. -/
theorem matchPat_inst_eq {lhs : AST} (hsf : SubstFree lhs)
    {t : AST} {bnds0 bnds : List (String × AST)} (hm : AST.matchPat lhs t bnds0 = some bnds) :
    AST.inst bnds lhs = t := by
  rw [← instStruct_eq_inst_substFree hsf]; exact matchPat_instStruct_eq hm
/-- The argument-list version (the original `matchPatList_inst_eq`). -/
theorem matchPatList_inst_eq {ps : List AST} (hsf : SubstFreeList ps)
    {ts : List AST} {bnds0 bnds : List (String × AST)} (hm : AST.matchPatList ps ts bnds0 = some bnds) :
    AST.instList bnds ps = ts := by
  rw [← instStructList_eq_instList_substFree hsf]; exact matchPatList_instStruct_eq hm

/-! ### The runtime step is a genuine rule application

The matcher correctness certifies the runtime: when `applyBaseRewrite` fires a (subst-free) base rule on a
term, the result really is the rule's right side instantiated at a substitution whose action on the left
side gives back the original term. So `t ~> t'` genuinely instances `lhs ~> rhs`. -/

/-- A successful base rewrite is a genuine rule application: there is a substitution `bnds` with
    `t = lhs·bnds` and `t' = rhs·bnds`. -/
theorem applyBaseRewrite_genuine {rd : RewriteDecl} {lhs rhs t t' : AST}
    (hsf : SubstFree lhs) (hrw : rd.rw = .base lhs rhs) (h : applyBaseRewrite rd t = some t') :
    ∃ bnds, AST.inst bnds lhs = t ∧ t' = AST.inst bnds rhs := by
  unfold applyBaseRewrite at h
  rw [hrw] at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨bnds, hm, ht'⟩ := h
  exact ⟨bnds, matchPat_inst_eq hsf hm, ht'.symm⟩

/-! ### Matcher completeness: the matcher finds every instance

The dual of `matchPat_inst_eq`: the matcher never misses a match. This mirrors the completeness half of
MORK's `VarRefRecheck` (the re-check is sound and, under the right groundness, complete). Here completeness
is unconditional, because a substitution is a function, so a pattern's instance has equal subterms at a
repeated variable's positions and the consistency test always passes. -/

/-- `bnds` agrees with a substitution `σ`: it binds each variable exactly as `σ` instantiates it. -/
def CompatS (σ bnds : List (String × AST)) : Prop :=
  ∀ v ty, bndLookup bnds v = some ty → ty = AST.inst σ (.var (.base v))

mutual
  /-- The matcher succeeds on any STRUCTURAL instance of ANY pattern (full language, including `Subst`),
      threading a `σ`-compatible accumulator. -/
  theorem matchPat_instStruct_complete {σ : List (String × AST)} :
      ∀ {lhs : AST} {bnds0 : List (String × AST)}, CompatS σ bnds0 →
        ∃ bnds, AST.matchPat lhs (AST.instStruct σ lhs) bnds0 = some bnds ∧ CompatS σ bnds
    | .var (.base x), bnds0, hc => by
        rw [instStruct_var_eq_inst]
        cases hfx : bnds0.find? (fun b => b.1 == x) with
        | some pr =>
            obtain ⟨a, t'⟩ := pr
            have ht' : t' = AST.inst σ (.var (.base x)) :=
              hc x t' (by unfold bndLookup; rw [hfx]; rfl)
            refine ⟨bnds0, ?_, hc⟩
            simp only [AST.matchPat]; rw [hfx]; simp only [ht', beq_self_eq_true, if_true]
        | none =>
            refine ⟨(x, AST.inst σ (.var (.base x))) :: bnds0, ?_, ?_⟩
            · simp only [AST.matchPat]; rw [hfx]
            · intro v ty hbl
              by_cases hxv : x = v
              · subst hxv; rw [bndLookup_cons_self] at hbl; injection hbl with hbl; rw [← hbl]
              · rw [bndLookup_cons_of_ne hxv] at hbl; exact hc v ty hbl
    | .var (.qualified i r), bnds0, hc => ⟨bnds0, by simp [AST.matchPat, AST.instStruct], hc⟩
    | .sexp l args, bnds0, hc => by
        obtain ⟨bnds, hb, hcb⟩ := matchPatList_instStruct_complete hc
        refine ⟨bnds, ?_, hcb⟩
        simp only [AST.instStruct, AST.matchPat, beq_self_eq_true, if_true]; exact hb
    | .subst pb pr pv, bnds0, hc => by
        obtain ⟨bnds1, hb1, hc1⟩ := matchPat_instStruct_complete (lhs := pb) hc
        obtain ⟨bnds, hb, hc2⟩ := matchPat_instStruct_complete (lhs := pr) hc1
        refine ⟨bnds, ?_, hc2⟩
        simp only [AST.instStruct, AST.matchPat, beq_self_eq_true, if_true]; rw [hb1]; exact hb
  /-- The argument-list version. -/
  theorem matchPatList_instStruct_complete {σ : List (String × AST)} :
      ∀ {args : List AST} {bnds0 : List (String × AST)}, CompatS σ bnds0 →
        ∃ bnds, AST.matchPatList args (AST.instStructList σ args) bnds0 = some bnds ∧ CompatS σ bnds
    | [], bnds0, hc => ⟨bnds0, by simp [AST.instStructList, AST.matchPatList], hc⟩
    | a :: as, bnds0, hc => by
        obtain ⟨bnds1, hb1, hc1⟩ := matchPat_instStruct_complete (lhs := a) hc
        obtain ⟨bnds, hb, hc2⟩ := matchPatList_instStruct_complete hc1
        refine ⟨bnds, ?_, hc2⟩
        simp only [AST.instStructList, AST.matchPatList]; rw [hb1]; exact hb
end

/-- Subst-free corollary: the matcher succeeds on any `inst`-instance (the original `matchPat_complete`). -/
theorem matchPat_complete {σ : List (String × AST)} {lhs : AST} (hsf : SubstFree lhs)
    {bnds0 : List (String × AST)} (hc : CompatS σ bnds0) :
    ∃ bnds, AST.matchPat lhs (AST.inst σ lhs) bnds0 = some bnds ∧ CompatS σ bnds := by
  rw [← instStruct_eq_inst_substFree hsf]; exact matchPat_instStruct_complete hc
/-- The argument-list version (the original `matchPatList_complete`). -/
theorem matchPatList_complete {σ : List (String × AST)} {args : List AST} (hsf : SubstFreeList args)
    {bnds0 : List (String × AST)} (hc : CompatS σ bnds0) :
    ∃ bnds, AST.matchPatList args (AST.instList σ args) bnds0 = some bnds ∧ CompatS σ bnds := by
  rw [← instStructList_eq_instList_substFree hsf]; exact matchPatList_instStruct_complete hc

/-- Matcher correctness, both directions, for the FULL pattern language (including `Subst`): a pattern
    matches a term exactly when the term is a STRUCTURAL instance of the pattern. -/
theorem matchPat_iff_instStruct {lhs t : AST} :
    (∃ bnds, AST.matchPat lhs t [] = some bnds) ↔ ∃ σ, AST.instStruct σ lhs = t := by
  constructor
  · rintro ⟨bnds, hm⟩; exact ⟨bnds, matchPat_instStruct_eq hm⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨bnds, hb, _⟩ :=
      matchPat_instStruct_complete (σ := σ) (bnds0 := []) (fun v ty hbl => by simp [bndLookup] at hbl)
    exact ⟨bnds, hb⟩

/-- Matcher correctness, both directions: a (subst-free) pattern matches a term exactly when the term is an
    `inst`-instance of the pattern. The subst-free corollary of `matchPat_iff_instStruct`. -/
theorem matchPat_iff_instance {lhs t : AST} (hsf : SubstFree lhs) :
    (∃ bnds, AST.matchPat lhs t [] = some bnds) ↔ ∃ σ, AST.inst σ lhs = t := by
  constructor
  · rintro ⟨bnds, hm⟩; exact ⟨bnds, matchPat_inst_eq hsf hm⟩
  · rintro ⟨σ, rfl⟩
    obtain ⟨bnds, hb, _⟩ :=
      matchPat_complete (σ := σ) (bnds0 := []) hsf (fun v ty hbl => by simp [bndLookup] at hbl)
    exact ⟨bnds, hb⟩

end MeTTaIL
