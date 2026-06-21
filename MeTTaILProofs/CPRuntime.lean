/-
Module: MeTTaILProofs.CPRuntime
Layer: Proofs
Purpose: Connect the first-order Critical Pair Theorem (`CriticalPairs`, over `FOTerm`) to the actual
  runtime relation `RewStep` over `AST`. A faithful embedding `emb : FOTerm → AST` (variables named by an
  injective `ν`, applications as `sexp`) is shown to simulate the FOTerm rewrite relation `Rstep` by the
  runtime's `RewStep` on the embedded (subst-free) fragment. The embedding commutes with substitution and
  with positions, the root case uses the matcher correctness of `MatcherCorrect` (a successful `matchPat` is
  exactly a rule instance), and the congruence case lines up `RewStep.arg` with descent into an argument
  position. This certifies that the rewriting the CPT reasons about is exactly what the runtime does.
Imports: MeTTaILProofs.CriticalPairs (FOTerm, Rstep, positions), MeTTaILProofs.MatcherCorrect (matcher
  correctness), MeTTaIL.Semantics.Context (RewStep), MeTTaIL.Semantics.Relation (Reduces)
Trusted boundary: none (fully proved)
Main exports: emb, emb_injective, emb_subst, emb_subAt, Rstep_to_RewStep (forward simulation)
Open obligations: premised (conditional) rewrites are out of scope, as is the `Subst`/binder fragment.
-/
import MeTTaILProofs.CriticalPairs
import MeTTaILProofs.MatcherCorrect
import MeTTaIL.Semantics.Context
import MeTTaIL.Semantics.Relation

namespace MeTTaIL.CP

variable (ν : Nat → String)

mutual
  /-- Free variables of a first-order term. -/
  def FOTerm.varsOf : FOTerm → List Nat
    | .var n => [n]
    | .app _ args => FOTerm.varsOfList args
  def FOTerm.varsOfList : List FOTerm → List Nat
    | [] => []
    | a :: as => a.varsOf ++ FOTerm.varsOfList as
end

mutual
  /-- The faithful embedding of a first-order term into the runtime AST: a variable becomes a base variable
      named by `ν`, an application becomes an `sexp`. -/
  def emb : FOTerm → AST
    | .var n => .var (.base (ν n))
    | .app f args => .sexp (.id f) (embList args)
  def embList : List FOTerm → List AST
    | [] => []
    | a :: as => emb a :: embList as
end

mutual
  /-- The embedding lands in the subst-free fragment. -/
  theorem emb_substFree : ∀ t : FOTerm, SubstFree (emb ν t)
    | .var _ => trivial
    | .app _ args => by simp only [emb, SubstFree]; exact embList_substFree args
  theorem embList_substFree : ∀ args : List FOTerm, SubstFreeList (embList ν args)
    | [] => trivial
    | a :: as => by simp only [embList, SubstFreeList]; exact ⟨emb_substFree a, embList_substFree as⟩
end

mutual
  /-- The embedding is injective (variables distinguished by the injective naming `ν`). -/
  theorem emb_injective (hν : Function.Injective ν) : ∀ {s t : FOTerm}, emb ν s = emb ν t → s = t
    | .var m, .var n, h => by simp only [emb, AST.var.injEq, DottedPath.base.injEq] at h; rw [hν h]
    | .var _, .app _ _, h => by simp [emb] at h
    | .app _ _, .var _, h => by simp [emb] at h
    | .app f args, .app g brgs, h => by
        simp only [emb, AST.sexp.injEq, Label.id.injEq] at h
        obtain ⟨rfl, hargs⟩ := h
        rw [embList_injective hν hargs]
  theorem embList_injective (hν : Function.Injective ν) :
      ∀ {as bs : List FOTerm}, embList ν as = embList ν bs → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [embList] at h
    | _ :: _, [], h => by simp [embList] at h
    | a :: as, b :: bs, h => by
        simp only [embList, List.cons.injEq] at h
        rw [emb_injective hν h.1, embList_injective hν h.2]
end

mutual
  /-- The embedding commutes with substitution: `emb` of a substituted term is the AST instance under any
      binding that matches the substitution on the term's variables. -/
  theorem emb_subst {σ : Nat → FOTerm} {bnds : List (String × AST)} :
      ∀ {t : FOTerm}, (∀ n ∈ t.varsOf, bndLookup bnds (ν n) = some (emb ν (σ n))) →
        emb ν (subst σ t) = AST.inst bnds (emb ν t)
    | .var n, h => by
        have hn := h n (by simp [FOTerm.varsOf])
        simp only [subst, emb]
        rw [inst_var_of_bndLookup hn]
    | .app f args, h => by
        simp only [subst, emb, AST.inst]
        congr 1
        exact embList_subst (fun n hn => h n hn)
  theorem embList_subst {σ : Nat → FOTerm} {bnds : List (String × AST)} :
      ∀ {args : List FOTerm}, (∀ n ∈ FOTerm.varsOfList args, bndLookup bnds (ν n) = some (emb ν (σ n))) →
        embList ν (substList σ args) = AST.instList bnds (embList ν args)
    | [], _ => rfl
    | a :: as, h => by
        simp only [substList, embList, AST.instList]
        rw [emb_subst (fun n hn => h n (List.mem_append_left _ hn)),
          embList_subst (fun n hn => h n (List.mem_append_right _ hn))]
end

mutual
  /-- Free variables transport across the embedding: the runtime variables of `emb t` are `t`'s first-order
      variables renamed by `ν`. -/
  theorem emb_varsOf : ∀ t : FOTerm, varsOf (emb ν t) = (FOTerm.varsOf t).map ν
    | .var _ => rfl
    | .app _ args => by simp only [emb, varsOf, FOTerm.varsOf]; exact emb_varsOfList args
  theorem emb_varsOfList :
      ∀ args : List FOTerm, varsOfList (embList ν args) = (FOTerm.varsOfList args).map ν
    | [] => rfl
    | a :: as => by
        simp only [embList, varsOfList, FOTerm.varsOfList, List.map_append]
        rw [emb_varsOf a, emb_varsOfList as]
end

/-- The embedding distributes over list append. -/
theorem embList_append : ∀ xs ys : List FOTerm, embList ν (xs ++ ys) = embList ν xs ++ embList ν ys
  | [], _ => rfl
  | x :: xs, ys => by simp only [List.cons_append, embList]; rw [embList_append xs ys]

/-- The binding list realising a first-order substitution `σ` over a chosen variable set, as the runtime
    expects: each first-order variable `n` is bound to `emb (σ n)` under the renamed name `ν n`. -/
def embSubst (σ : Nat → FOTerm) : List Nat → List (String × AST)
  | [] => []
  | n :: ns => (ν n, emb ν (σ n)) :: embSubst σ ns

/-- Looking a variable up in `embSubst` recovers the embedded substitution image. Injectivity of `ν` is
    what guarantees the name `ν n` resolves to its own entry and not a clash. -/
theorem embSubst_lookup (hν : Function.Injective ν) (σ : Nat → FOTerm) :
    ∀ {vs : List Nat} {n : Nat}, n ∈ vs → bndLookup (embSubst ν σ vs) (ν n) = some (emb ν (σ n))
  | [], _, hn => by simp at hn
  | m :: ms, n, hn => by
      simp only [embSubst]
      by_cases h : m = n
      · subst h; rw [bndLookup_cons_self]
      · rw [bndLookup_cons_of_ne (fun he => h (hν he)) (emb ν (σ m)) (embSubst ν σ ms)]
        exact embSubst_lookup hν σ ((List.mem_cons.mp hn).resolve_left (fun he => h he.symm))

/-- The runtime rewrite declaration embedding a first-order rule. -/
def embRule (l r : FOTerm) : RewriteDecl := { name := "emb", rw := .base (emb ν l) (emb ν r) }

/-- The runtime presentation embedding a first-order rewrite system: just its rules, embedded. -/
def embPres (R : List (FOTerm × FOTerm)) : Presentation :=
  .mk [] [] [] (R.map (fun lr => embRule ν lr.1 lr.2)) []

/-- An embedded rule sits in the embedded presentation. -/
theorem embRule_mem {R : List (FOTerm × FOTerm)} {l r : FOTerm} (hmem : (l, r) ∈ R) :
    embRule ν l r ∈ (embPres ν R).rewrites := by
  simp only [embPres, Presentation.rewrites]
  exact List.mem_map.mpr ⟨(l, r), hmem, rfl⟩

/-- Instantiating an embedded right-hand side under matcher bindings equals instantiating it under the
    read-off substitution, provided the bindings realise the substitution on the rule's variables (and the
    right-hand side introduces no fresh ones). Shared by the forward and backward root cases. -/
theorem inst_emb_agree (hν : Function.Injective ν) {bnds : List (String × AST)} {σ' : Nat → FOTerm}
    {l r : FOTerm} (hvr : ∀ n ∈ r.varsOf, n ∈ l.varsOf)
    (hbind : ∀ n ∈ l.varsOf, bndLookup bnds (ν n) = some (emb ν (σ' n))) :
    AST.inst bnds (emb ν r) = AST.inst (embSubst ν σ' l.varsOf) (emb ν r) := by
  apply inst_agree (emb_substFree ν r)
  intro v hv
  rw [emb_varsOf] at hv
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hv
  have hnl := hvr n hn
  rw [hbind n hnl, embSubst_lookup ν hν σ' hnl]

/-- The root case of the simulation: a rule firing at the root of a first-order term is a genuine runtime
    `RewStep` (via `Reduces`) between the embedded terms. This is where matcher correctness does the work:
    the embedded instance `emb (subst σ l)` matches the embedded pattern `emb l`, and the matcher's binding
    agrees with `σ` on the rule's variables, so the contractum is exactly `emb (subst σ r)`. -/
theorem Rstep_root (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)} {l r : FOTerm}
    (hvars : ∀ n ∈ r.varsOf, n ∈ l.varsOf) (hmem : (l, r) ∈ R) (σ : Nat → FOTerm) :
    RewStep (embPres ν R) (emb ν (subst σ l)) (emb ν (subst σ r)) := by
  have heL : emb ν (subst σ l) = AST.inst (embSubst ν σ l.varsOf) (emb ν l) :=
    emb_subst ν (fun n hn => embSubst_lookup ν hν σ hn)
  obtain ⟨bnds, hmatch0, hcompat⟩ :=
    matchPat_complete (σ := embSubst ν σ l.varsOf) (emb_substFree ν l) (bnds0 := [])
      (fun v ty hbl => by simp [bndLookup] at hbl)
  rw [← heL] at hmatch0
  have hred : Reduces (embPres ν R) (emb ν (subst σ l)) (AST.inst bnds (emb ν r)) :=
    reduces_base (embPres ν R) (embRule ν l r) (emb ν l) (emb ν r) (emb ν (subst σ l)) bnds
      (embRule_mem ν hmem) rfl hmatch0
  have hbind : ∀ n ∈ l.varsOf, bndLookup bnds (ν n) = some (emb ν (σ n)) := by
    intro n hnl
    obtain ⟨ty, hty⟩ :=
      matchPat_cover_sf (emb_substFree ν l) hmatch0
        (by rw [emb_varsOf]; exact List.mem_map.mpr ⟨n, hnl, rfl⟩)
    rw [hty, hcompat (ν n) ty hty, inst_var_of_bndLookup (embSubst_lookup ν hν σ hnl)]
  have hfinal : AST.inst bnds (emb ν r) = emb ν (subst σ r) := by
    rw [inst_emb_agree ν hν hvars hbind]
    exact (emb_subst ν (fun n hn => embSubst_lookup ν hν σ (hvars n hn))).symm
  exact RewStep.top (hfinal ▸ hred)

/-- The congruence case: a runtime step inside an argument lifts to a runtime step of the whole `sexp`,
    matching `RewStep.arg`. This realises descent into a first-order position as descent into an `sexp`. -/
theorem emb_congr {P : Presentation} (f : String) (args : List FOTerm) (i : Nat) (a w : FOTerm)
    (hi : args[i]? = some a) (hstep : RewStep P (emb ν a) (emb ν w)) :
    RewStep P (emb ν (.app f args)) (emb ν (.app f (args.set i w))) := by
  obtain ⟨hlt, ha⟩ := List.getElem?_eq_some_iff.mp hi
  have hsplit : args = args.take i ++ a :: args.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i args, List.drop_eq_getElem_cons hlt, ha]
  have hset : args.set i w = args.take i ++ w :: args.drop (i + 1) := List.set_eq_take_cons_drop w hlt
  have e1 : embList ν args = embList ν (args.take i) ++ emb ν a :: embList ν (args.drop (i + 1)) := by
    conv_lhs => rw [hsplit]
    rw [embList_append, embList]
  simp only [emb]
  rw [e1, hset, embList_append, embList]
  exact RewStep.arg hstep

/-- The forward simulation at a fixed position, by induction on the position: a rule matching at position
    `p` of `s` yields a runtime `RewStep` from `emb s` to `emb (repAt s p (subst σ r))`. -/
theorem Rstep_to_RewStep_at (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)} {l r : FOTerm}
    (hvars : ∀ n ∈ r.varsOf, n ∈ l.varsOf) (hmem : (l, r) ∈ R) (σ : Nat → FOTerm) :
    ∀ {s : FOTerm} (p : Pos), subAt s p = some (subst σ l) →
      RewStep (embPres ν R) (emb ν s) (emb ν (repAt s p (subst σ r)))
  | s, [], hsub => by
      simp only [subAt, Option.some.injEq] at hsub
      subst hsub
      simp only [repAt]
      exact Rstep_root ν hν hvars hmem σ
  | .var _, _ :: _, hsub => by simp [subAt] at hsub
  | .app f args, i :: p, hsub => by
      simp only [subAt] at hsub
      split at hsub
      · rename_i a hai
        have ih := Rstep_to_RewStep_at hν hvars hmem σ (s := a) p hsub
        have hcong := emb_congr ν f args i a (repAt a p (subst σ r)) hai ih
        have hrep : repAt (.app f args) (i :: p) (subst σ r)
            = .app f (args.set i (repAt a p (subst σ r))) := by simp only [repAt, hai]
        rw [hrep]; exact hcong
      · simp at hsub

/-- The forward simulation: every first-order rewrite step is a genuine runtime `RewStep` between the
    embedded terms. The first-order rewriting that the Critical Pair Theorem reasons about is exactly the
    runtime relation `RewStep`, restricted to the embedded fragment. The only hypothesis is the standard
    rewrite-system condition that right-hand sides introduce no fresh variables. -/
theorem Rstep_to_RewStep (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf)
    {s s' : FOTerm} (h : Rstep R s s') :
    RewStep (embPres ν R) (emb ν s) (emb ν s') := by
  obtain ⟨p, l, r, σ, hmem, hsub, hrep⟩ := h
  subst hrep
  exact Rstep_to_RewStep_at ν hν (hvars l r hmem) hmem σ p hsub

/-! ### Backward simulation: a runtime step on an embedded term comes from a first-order step.

The forward direction shows the first-order rewriting embeds into the runtime. For confluence transport we
also need the converse on the embedded fragment: every `RewStep` out of `emb s` lands on another embedded
term `emb s'` and is witnessed by a first-order `Rstep s s'`. The crux is `emb_inst_inv`, which lifts an
AST-level match back to a first-order substitution. Because `emb` is injective it has a left inverse, and
the substitution read off the bindings through that inverse is global (one function of the bindings), so the
two argument-list halves never need their substitutions reconciled. -/

/-- The first-order substitution read off a runtime binding list through the left inverse of `emb`. Only
    used in proofs (noncomputable), so the left inverse via choice is harmless. -/
noncomputable def σOf (bnds : List (String × AST)) : Nat → FOTerm :=
  fun n => match bndLookup bnds (ν n) with
    | some w => Function.invFun (emb ν) w
    | none => default

mutual
  /-- The inversion lemma: if instantiating `emb l` under `bnds` (which covers `l`'s variables) yields
      `emb t`, then `t` is `l` under the read-off substitution `σOf bnds`, and every bound value is itself an
      embedded term. This is the heart of the backward simulation. -/
  theorem emb_inst_inv (hν : Function.Injective ν) {bnds : List (String × AST)} :
      ∀ {l t : FOTerm}, (∀ n ∈ l.varsOf, ∃ w, bndLookup bnds (ν n) = some w) →
        AST.inst bnds (emb ν l) = emb ν t →
        subst (σOf ν bnds) l = t ∧ ∀ n ∈ l.varsOf, bndLookup bnds (ν n) = some (emb ν (σOf ν bnds n))
    | .var n, t, hcov, h => by
        have hinj : Function.Injective (emb ν) := fun _ _ he => emb_injective ν hν he
        obtain ⟨w, hw⟩ := hcov n (by simp [FOTerm.varsOf])
        rw [emb, inst_var_of_bndLookup hw] at h
        have hσ : σOf ν bnds n = t := by
          simp only [σOf, hw]; rw [h]; exact Function.leftInverse_invFun hinj t
        refine ⟨by simp only [subst]; exact hσ, ?_⟩
        intro m hm
        simp only [FOTerm.varsOf, List.mem_singleton] at hm
        subst hm; rw [hw, hσ]; exact congrArg some h
    | .app f args, t, hcov, h => by
        cases t with
        | var m => simp [emb, AST.inst] at h
        | app f' targs =>
            simp only [emb, AST.inst, AST.sexp.injEq, Label.id.injEq] at h
            obtain ⟨rfl, hl⟩ := h
            obtain ⟨hsub, hbind⟩ :=
              embList_inst_inv hν (by simpa [FOTerm.varsOf] using hcov) hl
            exact ⟨by simp only [subst]; rw [hsub], by simpa [FOTerm.varsOf] using hbind⟩
  theorem embList_inst_inv (hν : Function.Injective ν) {bnds : List (String × AST)} :
      ∀ {args targs : List FOTerm},
        (∀ n ∈ FOTerm.varsOfList args, ∃ w, bndLookup bnds (ν n) = some w) →
        AST.instList bnds (embList ν args) = embList ν targs →
        substList (σOf ν bnds) args = targs ∧
          ∀ n ∈ FOTerm.varsOfList args, bndLookup bnds (ν n) = some (emb ν (σOf ν bnds n))
    | [], targs, _, h => by
        cases targs with
        | nil => exact ⟨rfl, by simp [FOTerm.varsOfList]⟩
        | cons th tt => simp [embList, AST.instList] at h
    | a :: as, targs, hcov, h => by
        cases targs with
        | nil => simp [embList, AST.instList] at h
        | cons th tt =>
            simp only [embList, AST.instList, List.cons.injEq] at h
            obtain ⟨hh, htl⟩ := h
            obtain ⟨hsa, hba⟩ :=
              emb_inst_inv hν (fun n hn => hcov n (List.mem_append_left _ hn)) hh
            obtain ⟨hsas, hbas⟩ :=
              embList_inst_inv hν (fun n hn => hcov n (List.mem_append_right _ hn)) htl
            refine ⟨by simp only [substList]; rw [hsa, hsas], ?_⟩
            intro n hn
            rw [FOTerm.varsOfList, List.mem_append] at hn
            cases hn with
            | inl h' => exact hba n h'
            | inr h' => exact hbas n h'
end

/-- An embedded term that is an `sexp` came from an application. -/
theorem emb_eq_sexp_inv : ∀ {s : FOTerm} {lab : Label} {as : List AST},
    emb ν s = .sexp lab as → ∃ f sargs, s = .app f sargs ∧ lab = .id f ∧ as = embList ν sargs
  | .var n, _, _, h => by simp [emb] at h
  | .app f sargs, _, _, h => by
      simp only [emb, AST.sexp.injEq] at h
      exact ⟨f, sargs, rfl, h.1.symm, h.2.symm⟩

/-- An embedded term is never a `Subst`, so the `Subst`-context rewrite rules cannot fire on it. -/
theorem emb_ne_subst : ∀ (s : FOTerm) (b r : AST) (v : DottedPath), emb ν s ≠ .subst b r v
  | .var _, _, _, _ => by simp [emb]
  | .app _ _, _, _, _ => by simp [emb]

/-- Reading the element at the boundary of a split list. -/
theorem getElem?_mid {α : Type*} :
    ∀ (xs : List α) (a : α) (ys : List α), (xs ++ a :: ys)[xs.length]? = some a
  | [], _, _ => rfl
  | _ :: xs, a, ys => by
      simp only [List.cons_append, List.length_cons, List.getElem?_cons_succ]
      exact getElem?_mid xs a ys

/-- Setting the element at the boundary of a split list. -/
theorem set_mid {α : Type*} :
    ∀ (xs : List α) (a : α) (ys : List α) (b : α), (xs ++ a :: ys).set xs.length b = xs ++ b :: ys
  | [], _, _, _ => rfl
  | x :: xs, a, ys, b => by
      simp only [List.cons_append, List.length_cons, List.set_cons_succ]
      rw [set_mid xs a ys b]

/-- Inverting an embedded argument list split at an AST position: the split lands at a first-order
    argument, and the surrounding pieces are themselves embedded lists. -/
theorem embList_split_inv : ∀ {args : List FOTerm} {pre post : List AST} {b : AST},
    embList ν args = pre ++ b :: post →
    ∃ (a : FOTerm) (apre apost : List FOTerm),
      args = apre ++ a :: apost ∧ pre = embList ν apre ∧ b = emb ν a ∧ post = embList ν apost
  | [], _, _, _, h => by simp [embList] at h
  | a :: as, [], _, _, h => by
      simp only [embList, List.nil_append, List.cons.injEq] at h
      exact ⟨a, [], as, rfl, rfl, h.1.symm, h.2.symm⟩
  | a :: as, pre' :: pres, _, _, h => by
      simp only [embList, List.cons_append, List.cons.injEq] at h
      obtain ⟨a'', apre, apost, hargs, hpre, hb, hpost⟩ := embList_split_inv h.2
      exact ⟨a'', a :: apre, apost, by rw [hargs]; rfl, by rw [embList, ← h.1, hpre], hb, hpost⟩

/-- The root (top) case of the backward simulation: a `Reduces` step out of an embedded term lands on
    another embedded term and is witnessed by a first-order root rewrite. The matcher binding is lifted to
    a first-order substitution by `emb_inst_inv`. -/
theorem reduces_emb_to_Rstep (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf)
    {s : FOTerm} {u : AST} (h : Reduces (embPres ν R) (emb ν s) u) :
    ∃ s' : FOTerm, u = emb ν s' ∧ Rstep R s s' := by
  cases h with
  | step rd bnds bnds' hrd hm hph hu =>
      simp only [embPres, Presentation.rewrites, List.mem_map] at hrd
      obtain ⟨⟨l, r⟩, hmemR, hrdeq⟩ := hrd
      subst hrdeq
      simp only [embRule, Rewrite.conclusion, Rewrite.premises] at hm hph hu
      cases hph
      have hcov : ∀ m ∈ l.varsOf, ∃ w, bndLookup bnds (ν m) = some w := fun m hm' =>
        matchPat_cover_sf (emb_substFree ν l) hm
          (by rw [emb_varsOf]; exact List.mem_map.mpr ⟨m, hm', rfl⟩)
      obtain ⟨hsl, hbind⟩ :=
        emb_inst_inv ν hν hcov (matchPat_inst_eq (emb_substFree ν l) hm)
      refine ⟨subst (σOf ν bnds) r, ?_, ?_⟩
      · rw [hu, inst_emb_agree ν hν (hvars l r hmemR) hbind]
        exact (emb_subst ν (fun n hn => embSubst_lookup ν hν (σOf ν bnds) (hvars l r hmemR n hn))).symm
      · exact ⟨[], l, r, σOf ν bnds, hmemR, by simp only [subAt]; rw [hsl], by rw [repAt]⟩

/-- The backward simulation, by induction on the runtime derivation: every `RewStep` out of an embedded
    term lands on another embedded term and is witnessed by a first-order `Rstep`. The `Subst`-context
    cases are impossible because embedded terms are never `Subst`s. -/
theorem RewStep_to_Rstep_aux (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf) {es u : AST}
    (h : RewStep (embPres ν R) es u) :
    ∀ {s : FOTerm}, es = emb ν s → ∃ s' : FOTerm, u = emb ν s' ∧ Rstep R s s' := by
  induction h with
  | top hred => intro s hes; subst hes; exact reduces_emb_to_Rstep ν hν hvars hred
  | @arg lab pre post a a' hstep ih =>
      intro s hes
      obtain ⟨f, sargs, rfl, hlab, hsplit⟩ := emb_eq_sexp_inv ν hes.symm
      obtain ⟨afo, apre, apost, hsargs, hpre, hb, hpost⟩ := embList_split_inv ν hsplit.symm
      obtain ⟨a'', ha'', hstepR⟩ := ih (s := afo) hb
      refine ⟨.app f (apre ++ a'' :: apost), ?_, ?_⟩
      · subst hlab; subst hpre; subst hpost; subst ha''
        rw [emb, embList_append, embList]
      · subst hsargs
        obtain ⟨q, ll, rr, σ, hmem, hq, hrp⟩ := hstepR
        refine ⟨apre.length :: q, ll, rr, σ, hmem, ?_, ?_⟩
        · rw [subAt_app_cons, getElem?_mid]; exact hq
        · simp only [repAt, getElem?_mid]; rw [← hrp, set_mid]
  | @substB b b' r v hstep ih => intro s hes; exact absurd hes.symm (emb_ne_subst ν s b r v)
  | @substR b r r' v hstep ih => intro s hes; exact absurd hes.symm (emb_ne_subst ν s b r v)

/-- The backward simulation, packaged for an embedded source. -/
theorem RewStep_to_Rstep (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf) {s : FOTerm} {u : AST}
    (h : RewStep (embPres ν R) (emb ν s) u) : ∃ s' : FOTerm, u = emb ν s' ∧ Rstep R s s' :=
  RewStep_to_Rstep_aux ν hν hvars h rfl

/-- Forward simulation lifted to many steps: a first-order reduction sequence embeds as a runtime one. -/
theorem RstepMany_to_RewStep (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf) {s s' : FOTerm}
    (h : Relation.ReflTransGen (Rstep R) s s') :
    Relation.ReflTransGen (RewStep (embPres ν R)) (emb ν s) (emb ν s') :=
  Relation.ReflTransGen.lift (emb ν) (fun _ _ hab => Rstep_to_RewStep ν hν hvars hab) h

/-- Backward simulation lifted to many steps: a runtime reduction sequence out of an embedded term stays in
    the embedded fragment and comes from a first-order reduction sequence. -/
theorem RewStepMany_to_Rstep (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf) {s : FOTerm} {u : AST}
    (h : Relation.ReflTransGen (RewStep (embPres ν R)) (emb ν s) u) :
    ∃ s' : FOTerm, u = emb ν s' ∧ Relation.ReflTransGen (Rstep R) s s' := by
  induction h with
  | refl => exact ⟨s, rfl, .refl⟩
  | @tail b c _ hlast ih =>
      obtain ⟨smid, hmid, hsteps⟩ := ih
      subst hmid
      obtain ⟨s', hc, hstepR⟩ := RewStep_to_Rstep ν hν hvars hlast
      exact ⟨s', hc, hsteps.tail hstepR⟩

/-- Confluence transport: if the first-order rewrite system is confluent (as the Critical Pair Theorem
    certifies under left-linearity and joinable critical pairs), then the runtime relation `RewStep` is
    confluent on the embedded first-order fragment. This carries the CPT's confluence to the actual runtime
    relation, closing the model-mismatch compromise for the first-order fragment. -/
theorem RewStep_confluent_on_emb (hν : Function.Injective ν) {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ r.varsOf, n ∈ l.varsOf)
    (hconf : Confluent (Rstep R)) {s : FOTerm} {u1 u2 : AST}
    (h1 : Relation.ReflTransGen (RewStep (embPres ν R)) (emb ν s) u1)
    (h2 : Relation.ReflTransGen (RewStep (embPres ν R)) (emb ν s) u2) :
    Joinable (RewStep (embPres ν R)) u1 u2 := by
  obtain ⟨s1, hu1, hsteps1⟩ := RewStepMany_to_Rstep ν hν hvars h1
  obtain ⟨s2, hu2, hsteps2⟩ := RewStepMany_to_Rstep ν hν hvars h2
  obtain ⟨w, hw1, hw2⟩ := hconf s s1 s2 hsteps1 hsteps2
  subst hu1; subst hu2
  exact ⟨emb ν w, RstepMany_to_RewStep ν hν hvars hw1, RstepMany_to_RewStep ν hν hvars hw2⟩

/-! ### A concrete instance: the projection system embeds and the bridge fires

The bridge is parameterized by any injective naming `ν`. To witness that it is not vacuous, here is a
concrete injective naming and the projection system `f(x) -> x` (the same `projSys` whose first-order local
confluence is proved in `CriticalPairs`), with a genuine runtime step obtained from a first-order one. -/

/-- A concrete injective naming: `n` maps to the string of `n` copies of `'a'`. -/
def vname (n : Nat) : String := String.ofList (List.replicate n 'a')

theorem vname_injective : Function.Injective vname := by
  intro m n h
  have hd : (vname m).toList = (vname n).toList := congrArg String.toList h
  rw [vname, vname, String.toList_ofList, String.toList_ofList] at hd
  simpa [List.length_replicate] using congrArg List.length hd

/-- The projection rule introduces no fresh right-hand-side variables. -/
theorem hvars_projSys : ∀ l r, (l, r) ∈ projSys → ∀ n ∈ r.varsOf, n ∈ l.varsOf := by
  intro l r hm n hn
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  simpa [FOTerm.varsOf, FOTerm.varsOfList] using hn

/-- Non-vacuity of the forward simulation: the first-order step `f(a) -> a` is a genuine runtime `RewStep`
    between the embedded terms. -/
example : RewStep (embPres vname projSys)
    (emb vname (.app "f" [.app "a" []])) (emb vname (.app "a" [])) :=
  Rstep_to_RewStep vname vname_injective hvars_projSys
    ⟨[], .app "f" [.var 0], .var 0, fun _ => .app "a" [], by simp [projSys], rfl, rfl⟩

/-- Non-vacuity of the backward simulation: that same runtime step descends to a first-order step. -/
example : ∃ s', emb vname (.app "a" []) = emb vname s' ∧ Rstep projSys (.app "f" [.app "a" []]) s' :=
  RewStep_to_Rstep vname vname_injective hvars_projSys
    (Rstep_to_RewStep vname vname_injective hvars_projSys
      ⟨[], .app "f" [.var 0], .var 0, fun _ => .app "a" [], by simp [projSys], rfl, rfl⟩)

end MeTTaIL.CP
