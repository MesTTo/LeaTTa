-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.ConditionalCP
Layer: Proofs
Purpose: Confluence of the PREMISED (conditional) rewrite fragment, the part the unconditional Critical
  Pair Theorem (`CriticalPairs`) does not reach. A presentation's premised rewrites (the congruence/context
  rules par1, par2, RNew, and genuine side-conditioned rules) form an oriented conditional term rewrite
  system. Following the standard theory (Avenhaus-Loria-Saenz 1994; Dershowitz-Okada-Sivakumar 1987; Lucas,
  JLAMP 2024), this module:
    * models a conditional rule and the STRATIFIED oriented conditional rewrite relation `CRstep` (a rule
      fires when its left side matches and each condition `s ~> t` holds at a strictly lower level; the
      level keeps the definition well founded, the route to level-confluence in the literature),
    * proves the structural facts (level monotonicity, context congruence, the conditional Parallel Moves
      Lemma) directly, since a rule's conditions are about its own substitution and are untouched by a
      rewrite at a parallel or surrounding position,
    * proves the conditional Critical Pair Lemma soundness direction `c_localConfluent_of_joins`: a system
      whose conditional critical pairs (`CCPJ`) and conditional variable pairs (`CVarJ`) are joinable is
      locally confluent. These are exactly the two joinability obligations of Lucas Theorem 43 (the
      EXTENDED conditional critical pairs = proper critical pairs together with the conditional variable
      pairs), supplied here as hypotheses just as the unconditional `CPJ` is in `CriticalPairs`,
    * chains it with Newman's lemma for the headline `c_confluent_of_joins`: a terminating conditional
      system whose extended conditional critical pairs are joinable is confluent.
  This is the soundness ("if") direction; deciding the conditional critical pairs by conditional narrowing
  is out of scope, as the unconditional `CPJ` decision is in `CriticalPairs`. The position algebra and the
  substitution lemmas are reused verbatim from `CriticalPairs` (they are relation-independent).
Imports: MeTTaILProofs.CriticalPairs (FOTerm, positions, subAt/repAt/subst, the position algebra, Newman)
Trusted boundary: none (fully proved)
Main exports: CRule, CRstepN, CRstep, CRstepN_mono, crstep_context, crstep_parallel_join, CCPJ, CVarJ,
  c_localConfluent_of_joins, c_confluent_of_joins
Open obligations: deciding the conditional critical pairs (conditional narrowing) to discharge `CCPJ`/`CVarJ`
  automatically is future work, as is the completeness ("only if") direction.
-/
import MeTTaILProofs.CriticalPairs

namespace MeTTaIL.CP

/-- A conditional rewrite rule: a left side, a right side, and a list of oriented conditions `(s, t)`, each
    read as `s` reduces to `t`. A presentation's premised rewrite `let s ~> t in lhs ~> rhs` is a rule of
    this shape; a premise-free rule has `conds = []`. -/
structure CRule where
  lhs : FOTerm
  rhs : FOTerm
  conds : List (FOTerm × FOTerm)
deriving Inhabited

/-- The stratified oriented conditional rewrite relation at level `n`. A rule fires at level `n+1` when its
    left side matches at some position under a substitution `σ` and each condition `s ~> t` holds, read as a
    reduction `subst σ s ~>* subst σ t` at the strictly lower level `n`. Level `0` is empty. Stratifying by
    level keeps the recursion well founded (conditions are checked with fewer levels available) and is the
    standard device behind level-confluence of conditional systems. -/
def CRstepN (R : List CRule) : Nat → FOTerm → FOTerm → Prop
  | 0, _, _ => False
  | n + 1, t, t' =>
      ∃ (p : Pos) (rule : CRule) (σ : Nat → FOTerm),
        rule ∈ R ∧ subAt t p = some (subst σ rule.lhs) ∧
        (∀ c ∈ rule.conds, Relation.ReflTransGen (CRstepN R n) (subst σ c.1) (subst σ c.2)) ∧
        t' = repAt t p (subst σ rule.rhs)

/-- The oriented conditional rewrite relation: a step that fires at some level. -/
def CRstep (R : List CRule) (t t' : FOTerm) : Prop := ∃ n, CRstepN R n t t'

/-! ### Level monotonicity

More levels only allow more steps. This lets two steps that fire at different levels be brought to a common
level, and lets the conditional relation be treated as a single relation. -/

/-- Each level includes the one below it. -/
theorem CRstepN_le_succ (R : List CRule) :
    ∀ n {t t' : FOTerm}, CRstepN R n t t' → CRstepN R (n + 1) t t'
  | 0 => fun h => absurd h id
  | k + 1 => fun h => by
      obtain ⟨p, rule, σ, hmem, hsub, hconds, heq⟩ := h
      exact ⟨p, rule, σ, hmem, hsub,
        fun c hc => (hconds c hc).mono (fun _ _ hab => CRstepN_le_succ R k hab), heq⟩

/-- A step at level `m` is a step at any higher level `n`. -/
theorem CRstepN_mono (R : List CRule) {m n : Nat} (hmn : m ≤ n) {t t' : FOTerm}
    (h : CRstepN R m t t') : CRstepN R n t t' := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact CRstepN_le_succ R _ ih

/-- A reduction sequence at level `m` is a reduction sequence at any higher level. -/
theorem crstepN_many_mono (R : List CRule) {m n : Nat} (hmn : m ≤ n) {t t' : FOTerm}
    (h : Relation.ReflTransGen (CRstepN R m) t t') : Relation.ReflTransGen (CRstepN R n) t t' :=
  h.mono (fun _ _ hab => CRstepN_mono R hmn hab)

/-- Any level-`n` step is a conditional step. -/
theorem crstep_of_levelN (R : List CRule) {n : Nat} {t t' : FOTerm} (h : CRstepN R n t t') :
    CRstep R t t' := ⟨n, h⟩

/-- A level-`n` reduction sequence is a conditional reduction sequence. -/
theorem crstepMany_of_levelN (R : List CRule) {n : Nat} {t t' : FOTerm}
    (h : Relation.ReflTransGen (CRstepN R n) t t') : Relation.ReflTransGen (CRstep R) t t' :=
  h.mono (fun _ _ hab => crstep_of_levelN R hab)

/-! ### Context congruence

A conditional rewrite inside any context is again a conditional rewrite at the SAME level, because the
rule's conditions concern its own substitution and are unaffected by the surrounding context. From this the
whole reduce-inside-a-context toolkit lifts to the conditional relation. -/

/-- A level-`n` step inside any context is a level-`n` step: the conditions are unchanged. -/
theorem crstepN_context (R : List CRule) (n : Nat) {t s s' : FOTerm} {p : Pos}
    (hsub : subAt t p = some s) (hstep : CRstepN R n s s') : CRstepN R n t (repAt t p s') := by
  cases n with
  | zero => exact absurd hstep id
  | succ k =>
      obtain ⟨p0, rule, σ, hmem, hs0, hconds, hs'⟩ := hstep
      refine ⟨p ++ p0, rule, σ, hmem, ?_, hconds, ?_⟩
      · rw [subAt_append, hsub]; exact hs0
      · rw [hs', repAt_append_of_subAt hsub]

/-- A conditional step inside any context is a conditional step. -/
theorem crstep_context (R : List CRule) {t s s' : FOTerm} {p : Pos}
    (hsub : subAt t p = some s) (hstep : CRstep R s s') : CRstep R t (repAt t p s') := by
  obtain ⟨n, hn⟩ := hstep
  exact ⟨n, crstepN_context R n hsub hn⟩

/-- A conditional step lifts into any context regardless of what currently sits at the position. -/
theorem crstep_context_gen (R : List CRule) {t : FOTerm} {p : Pos} {s a a' : FOTerm}
    (h : subAt t p = some s) (hstep : CRstep R a a') :
    CRstep R (repAt t p a) (repAt t p a') := by
  have key := crstep_context R (subAt_repAt_self h a) hstep
  rwa [repAt_repAt_same] at key

/-- A whole conditional reduction sequence lifts into any context. -/
theorem crstepMany_context (R : List CRule) {t : FOTerm} {p : Pos} {s s' : FOTerm}
    (h : subAt t p = some s) (hsteps : Relation.ReflTransGen (CRstep R) s s') :
    Relation.ReflTransGen (CRstep R) (repAt t p s) (repAt t p s') :=
  Relation.ReflTransGen.lift (repAt t p ·) (fun _ _ hst => crstep_context_gen R h hst) hsteps

/-! ### Bounding the level of a reduction, and firing a rule

A finite reduction sequence (and a rule's finite list of conditions) only uses finitely many levels, so a
common bound exists. This lets a rule with conditions be fired as a single conditional step, working with
`CRstep` and `ReflTransGen (CRstep R)` directly rather than juggling explicit levels. -/

/-- A conditional reduction sequence runs at some single level. -/
theorem crstepMany_levelN (R : List CRule) {a b : FOTerm}
    (h : Relation.ReflTransGen (CRstep R) a b) : ∃ n, Relation.ReflTransGen (CRstepN R n) a b := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | tail _ hstep ih =>
      obtain ⟨n1, hn1⟩ := ih
      obtain ⟨n2, hn2⟩ := hstep
      exact ⟨max n1 n2,
        (crstepN_many_mono R (le_max_left n1 n2) hn1).tail (CRstepN_mono R (le_max_right n1 n2) hn2)⟩

/-- A rule's conditions, all holding as conditional reductions, hold at a single common level. -/
theorem conds_common_level (R : List CRule) (σ : Nat → FOTerm) :
    ∀ (conds : List (FOTerm × FOTerm)),
      (∀ c ∈ conds, Relation.ReflTransGen (CRstep R) (subst σ c.1) (subst σ c.2)) →
      ∃ n, ∀ c ∈ conds, Relation.ReflTransGen (CRstepN R n) (subst σ c.1) (subst σ c.2)
  | [], _ => ⟨0, fun _ hc => absurd hc List.not_mem_nil⟩
  | c0 :: cs, h => by
      obtain ⟨n0, hn0⟩ := conds_common_level R σ cs (fun c hc => h c (List.mem_cons_of_mem _ hc))
      obtain ⟨n1, hn1⟩ := crstepMany_levelN R (h c0 List.mem_cons_self)
      refine ⟨max n0 n1, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hcs
      · exact crstepN_many_mono R (le_max_right n0 n1) hn1
      · exact crstepN_many_mono R (le_max_left n0 n1) (hn0 c hcs)

/-- Fire a rule: if its left side matches at a position and all its conditions hold as conditional
    reductions, the contractum is a conditional step. -/
theorem crstep_fire (R : List CRule) {t : FOTerm} {p : Pos} {rule : CRule} {σ : Nat → FOTerm}
    (hmem : rule ∈ R) (hsub : subAt t p = some (subst σ rule.lhs))
    (hconds : ∀ c ∈ rule.conds, Relation.ReflTransGen (CRstep R) (subst σ c.1) (subst σ c.2)) :
    CRstep R t (repAt t p (subst σ rule.rhs)) := by
  obtain ⟨n, hn⟩ := conds_common_level R σ rule.conds hconds
  exact ⟨n + 1, p, rule, σ, hmem, hsub, hn, rfl⟩

/-- Invert a conditional step into its data, with the conditions as conditional reductions. -/
theorem crstep_inv (R : List CRule) {t t' : FOTerm} (h : CRstep R t t') :
    ∃ (p : Pos) (rule : CRule) (σ : Nat → FOTerm),
      rule ∈ R ∧ subAt t p = some (subst σ rule.lhs) ∧
      (∀ c ∈ rule.conds, Relation.ReflTransGen (CRstep R) (subst σ c.1) (subst σ c.2)) ∧
      t' = repAt t p (subst σ rule.rhs) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn id
  | succ k =>
      obtain ⟨p, rule, σ, hmem, hsub, hconds, heq⟩ := hn
      exact ⟨p, rule, σ, hmem, hsub, fun c hc => crstepMany_of_levelN R (hconds c hc), heq⟩

/-! ### Joinability helpers and the conditional Parallel Moves Lemma -/

/-- Joinability of conditional reductions lifts into any context. -/
theorem cjoinable_context (R : List CRule) {t : FOTerm} {p : Pos} {s a b : FOTerm}
    (h : subAt t p = some s) (hab : Joinable (CRstep R) a b) :
    Joinable (CRstep R) (repAt t p a) (repAt t p b) := by
  obtain ⟨c, hac, hbc⟩ := hab
  refine ⟨repAt t p c, ?_, ?_⟩
  · have key := crstepMany_context R (subAt_repAt_self h a) hac
    rwa [repAt_repAt_same, repAt_repAt_same] at key
  · have key := crstepMany_context R (subAt_repAt_self h b) hbc
    rwa [repAt_repAt_same, repAt_repAt_same] at key

/-- Joinability of conditional reductions is symmetric (the relation-generic `Joinable.symm`). -/
theorem cjoinable_symm (R : List CRule) {a b : FOTerm} (h : Joinable (CRstep R) a b) :
    Joinable (CRstep R) b a := h.symm

/-- The conditional Parallel Moves Lemma: two conditional steps at parallel positions are joinable. Each
    rule's conditions are about its own substitution and its own position, so firing one rule does not
    disturb the other's match or conditions; the two reducts join by the position algebra. -/
theorem crstep_parallel_join (R : List CRule) {t t1 t2 : FOTerm} {p q : Pos}
    {rule1 rule2 : CRule} {σ1 σ2 : Nat → FOTerm} (hpq : Parallel p q)
    (hm1 : rule1 ∈ R) (hs1 : subAt t p = some (subst σ1 rule1.lhs))
    (hc1 : ∀ c ∈ rule1.conds, Relation.ReflTransGen (CRstep R) (subst σ1 c.1) (subst σ1 c.2))
    (ht1 : t1 = repAt t p (subst σ1 rule1.rhs))
    (hm2 : rule2 ∈ R) (hs2 : subAt t q = some (subst σ2 rule2.lhs))
    (hc2 : ∀ c ∈ rule2.conds, Relation.ReflTransGen (CRstep R) (subst σ2 c.1) (subst σ2 c.2))
    (ht2 : t2 = repAt t q (subst σ2 rule2.rhs)) :
    Joinable (CRstep R) t1 t2 := by
  subst ht1 ht2
  refine ⟨repAt (repAt t p (subst σ1 rule1.rhs)) q (subst σ2 rule2.rhs),
    Relation.ReflTransGen.single ?_, Relation.ReflTransGen.single ?_⟩
  · exact crstep_fire R hm2 (by rw [subAt_repAt_parallel hpq]; exact hs2) hc2
  · have hfire := crstep_fire R hm1 (t := repAt t q (subst σ2 rule2.rhs)) (p := p) (σ := σ1)
      (by rw [subAt_repAt_parallel hpq.symm]; exact hs1) hc1
    rw [repAt_repAt_parallel hpq]; exact hfire

/-! ### The conditional critical pair theorem (soundness, Lucas Theorem 43)

The two joinability obligations are the EXTENDED conditional critical pairs: the proper conditional critical
pairs `CCPJ` (non-variable overlaps of two rules, joinable WHEN both rules' conditions hold) and the
conditional variable pairs `CVarJ` (an inner redex inside the image of a variable of an outer rule). They
are supplied as hypotheses, exactly as the unconditional `CPJ` is in `CriticalPairs`. -/

/-- Conditional critical pairs joinable: every non-variable overlap of two rules, when both rules'
    conditions hold, gives a joinable peak (the proper conditional critical pairs). -/
def CCPJ (R : List CRule) : Prop :=
  ∀ (rule1 rule2 : CRule) (o : Pos) (lo : FOTerm) (θ1 θ2 : Nat → FOTerm),
    rule1 ∈ R → rule2 ∈ R →
    subAt rule1.lhs o = some lo → (∀ y, lo ≠ .var y) → subst θ1 lo = subst θ2 rule2.lhs →
    (∀ c ∈ rule1.conds, Relation.ReflTransGen (CRstep R) (subst θ1 c.1) (subst θ1 c.2)) →
    (∀ c ∈ rule2.conds, Relation.ReflTransGen (CRstep R) (subst θ2 c.1) (subst θ2 c.2)) →
    Joinable (CRstep R) (subst θ1 rule1.rhs) (repAt (subst θ1 rule1.lhs) o (subst θ2 rule2.rhs))

/-- Conditional variable pairs joinable: an inner redex inside the image of a variable `x` of an outer
    rule, at position `ov ++ q`, gives a joinable peak when both rules' conditions hold. This is the
    conditional variable-pair obligation; for left-linear systems it is discharged by reduce-all-copies. -/
def CVarJ (R : List CRule) : Prop :=
  ∀ (rule1 rule2 : CRule) (ov : Pos) (x : Nat) (q : Pos) (θ1 θ2 : Nat → FOTerm),
    rule1 ∈ R → rule2 ∈ R →
    subAt rule1.lhs ov = some (.var x) →
    subAt (θ1 x) q = some (subst θ2 rule2.lhs) →
    (∀ c ∈ rule1.conds, Relation.ReflTransGen (CRstep R) (subst θ1 c.1) (subst θ1 c.2)) →
    (∀ c ∈ rule2.conds, Relation.ReflTransGen (CRstep R) (subst θ2 c.1) (subst θ2 c.2)) →
    Joinable (CRstep R) (subst θ1 rule1.rhs)
      (repAt (subst θ1 rule1.lhs) (ov ++ q) (subst θ2 rule2.rhs))

/-- The nested-overlap dispatch: when one redex sits inside the other, the conditional peak is joinable, by
    the conditional variable pairs (`CVarJ`, overlap below a variable) or the conditional critical pairs
    (`CCPJ`, non-variable overlap), separated by the positions-of-a-substitution decomposition. -/
theorem c_localConfluence_nested (R : List CRule) (hccpj : CCPJ R) (hcvarj : CVarJ R)
    {t : FOTerm} {p1 o : Pos} {rule1 rule2 : CRule} {θ1 θ2 : Nat → FOTerm}
    (hm1 : rule1 ∈ R) (hs1 : subAt t p1 = some (subst θ1 rule1.lhs))
    (hc1 : ∀ c ∈ rule1.conds, Relation.ReflTransGen (CRstep R) (subst θ1 c.1) (subst θ1 c.2))
    (hm2 : rule2 ∈ R) (hs2 : subAt t (p1 ++ o) = some (subst θ2 rule2.lhs))
    (hc2 : ∀ c ∈ rule2.conds, Relation.ReflTransGen (CRstep R) (subst θ2 c.1) (subst θ2 c.2)) :
    Joinable (CRstep R) (repAt t p1 (subst θ1 rule1.rhs)) (repAt t (p1 ++ o) (subst θ2 rule2.rhs)) := by
  have hsub : subAt (subst θ1 rule1.lhs) o = some (subst θ2 rule2.lhs) := by
    rw [subAt_append, hs1] at hs2; simpa using hs2
  rw [repAt_append_of_subAt hs1]
  apply cjoinable_context R hs1
  rcases subAt_subst_dichotomy θ1 rule1.lhs o hsub with ⟨lo, hlo, hw⟩ | ⟨ov, x, q, hov, hoq, hq⟩
  · cases lo with
    | var x =>
        have hqx : subAt (θ1 x) [] = some (subst θ2 rule2.lhs) := by
          simp only [subAt]; exact congrArg some hw.symm
        have := hcvarj rule1 rule2 o x [] θ1 θ2 hm1 hm2 hlo hqx hc1 hc2
        simpa using this
    | app g largs =>
        exact hccpj rule1 rule2 o (.app g largs) θ1 θ2 hm1 hm2 hlo (by simp) hw.symm hc1 hc2
  · rw [hoq]
    exact hcvarj rule1 rule2 ov x q θ1 θ2 hm1 hm2 hov hq hc1 hc2

/-- The conditional Critical Pair Theorem (soundness): a conditional system whose extended conditional
    critical pairs (the proper critical pairs `CCPJ` and the variable pairs `CVarJ`) are joinable is locally
    confluent. The three cases (disjoint, variable overlap, critical pair) are dispatched by the position
    trichotomy, exactly as in the unconditional `localConfluent_of_CPJ`. -/
theorem c_localConfluent_of_joins (R : List CRule) (hccpj : CCPJ R) (hcvarj : CVarJ R) :
    LocallyConfluent (CRstep R) := by
  intro t t1 t2 h1 h2
  obtain ⟨p1, rule1, θ1, hm1, hs1, hc1, rfl⟩ := crstep_inv R h1
  obtain ⟨p2, rule2, θ2, hm2, hs2, hc2, rfl⟩ := crstep_inv R h2
  rcases pos_trichotomy p1 p2 with hpar | ⟨o, rfl⟩ | ⟨o, rfl⟩
  · exact crstep_parallel_join R hpar hm1 hs1 hc1 rfl hm2 hs2 hc2 rfl
  · exact c_localConfluence_nested R hccpj hcvarj hm1 hs1 hc1 hm2 hs2 hc2
  · exact cjoinable_symm R (c_localConfluence_nested R hccpj hcvarj hm2 hs2 hc2 hm1 hs1 hc1)

/-- The conditional Knuth-Bendix-Huet criterion (soundness): a terminating conditional system whose
    extended conditional critical pairs are joinable is confluent. Local confluence from the conditional
    Critical Pair Theorem, confluence from Newman's lemma. This is the premised-rule counterpart of
    `confluent_of_CPJ`. -/
theorem c_confluent_of_joins (R : List CRule) (hccpj : CCPJ R) (hcvarj : CVarJ R)
    (hwf : WellFounded (fun b a => CRstep R a b)) : Confluent (CRstep R) :=
  newman (CRstep R) hwf (c_localConfluent_of_joins R hccpj hcvarj)

/-! ### Non-vacuity witnesses

The conditional relation genuinely fires conditional steps using a strictly lower level, and the
conditional Critical Pair Theorem yields a real local-confluence theorem. -/

/-- A two-rule conditional system: `a ~> b` (premise-free), and `g ~> h` conditioned on `a ~>* b`. -/
def csys : List CRule :=
  [⟨.app "a" [], .app "b" [], []⟩, ⟨.app "g" [], .app "h" [], [(.app "a" [], .app "b" [])]⟩]

/-- The conditional relation genuinely fires a conditional step: `g ~> h` holds because its condition
    `a ~>* b` holds at the lower level (`a ~> b` by the first rule). This is a real level-2 reduction, so
    the stratified relation is not degenerate. -/
theorem cond_step_demo : CRstep csys (.app "g" []) (.app "h" []) := by
  have hab : CRstep csys (.app "a" []) (.app "b" []) :=
    crstep_fire csys (rule := ⟨.app "a" [], .app "b" [], []⟩) (σ := fun _ => .var 0) (p := [])
      (by simp [csys]) (by simp [subst, substList, subAt]) (by simp)
  have hgh := crstep_fire csys (rule := ⟨.app "g" [], .app "h" [], [(.app "a" [], .app "b" [])]⟩)
    (σ := fun _ => .var 0) (p := []) (t := .app "g" [])
    (by simp [csys]) (by simp [subst, substList, subAt])
    (by intro c hc
        simp only [List.mem_singleton] at hc; subst hc
        simpa [subst, substList] using Relation.ReflTransGen.single hab)
  simpa [subst, substList, repAt] using hgh

/-- A single ground conditional rule: `g ~> h` conditioned on the (trivially true) `a ~>* a`. -/
def gsys : List CRule := [⟨.app "g" [], .app "h" [], [(.app "a" [], .app "a" [])]⟩]

/-- `gsys` has no conditional variable pairs: its left side is ground (no variable position). -/
theorem cvarj_gsys : CVarJ gsys := by
  intro rule1 _ ov x _ _ _ hm1 _ hov _ _ _
  exfalso
  simp only [gsys, List.mem_singleton] at hm1
  subst hm1
  cases ov with
  | nil => simp [subAt] at hov
  | cons i ov' => simp [subAt] at hov

/-- `gsys` has joinable conditional critical pairs: its only non-variable overlap is the root self-overlap,
    whose two sides are the same ground right side. -/
theorem ccpj_gsys : CCPJ gsys := by
  intro rule1 rule2 o lo θ1 θ2 hm1 hm2 hlo _ _ _ _
  simp only [gsys, List.mem_singleton] at hm1 hm2
  subst hm1; subst hm2
  cases o with
  | nil =>
      simp only [subAt, Option.some.injEq] at hlo; subst hlo
      simp only [subst, substList, repAt]
      exact ⟨.app "h" [], .refl, .refl⟩
  | cons i o' => exfalso; simp [subAt] at hlo

/-- The conditional Critical Pair Theorem instantiated: `gsys` is locally confluent. This witnesses that
    `c_localConfluent_of_joins` is not vacuous. -/
theorem locallyConfluent_gsys : LocallyConfluent (CRstep gsys) :=
  c_localConfluent_of_joins gsys ccpj_gsys cvarj_gsys

end MeTTaIL.CP
