-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.CriticalPairs
Layer: Proofs
Purpose: The Critical Pair Theorem (soundness direction, left-linear, first-order), over a clean term
  model. The runtime's confluence story already has Newman's lemma (terminating + locally confluent implies
  confluent) and the deterministic case; this module supplies the overlap analysis that derives local
  confluence. It develops first-order terms with positions and a subterm/replace algebra, then proves every
  local peak joinable, dispatched by the position trichotomy into the three classical cases: disjoint redexes
  (the Parallel Moves Lemma `rstep_parallel_join`), an overlap below a variable (`localConfluence_variable`,
  joined by reduce-all-copies and the reduct-matching `subst_update_eq_repAt` using left-linearity), and a
  non-variable overlap (the critical pair, found by the positions-of-a-substitution decomposition
  `subAt_subst_dichotomy` and discharged by the assumed `CPJ` hypothesis). The headline `localConfluent_of_CPJ`
  says a left-linear system whose critical pairs are joinable is locally confluent; `confluent_of_CPJ` chains
  it with Newman. This is the soundness ("if") direction with `CPJ` supplied as a hypothesis: there is no
  completeness direction and no unification machinery to enumerate or decide critical pairs. The model is the
  standard one of the rewriting literature (and of MORK's critical-pair engine): terms are variables or
  applications.
Imports: MeTTaILProofs.Newman (the abstract ARS layer: Joinable, LocallyConfluent, Confluent, newman)
Trusted boundary: none (fully proved)
Main exports: FOTerm, Pos, subAt, repAt, Parallel, subAt_repAt_parallel, repAt_repAt_parallel, subst,
  Rstep, rstep_parallel_join, rstep_context, rstepMany_context, subst_reduces, subAt_subst_dichotomy,
  subst_update_eq_repAt, LeftLinear, CPJ, localConfluence_variable, localConfluent_of_CPJ, confluent_of_CPJ
Open obligations: the completeness direction of the Critical Pair Lemma and a unification procedure to
  compute and decide critical pairs (so `CPJ` could be discharged automatically) are future work.
-/
import Mathlib.Tactic
import MeTTaILProofs.Newman

namespace MeTTaIL.CP

/-- A first-order term: a variable (indexed by a natural number) or a function symbol applied to
    arguments. This is the standard term model of the rewriting literature. -/
inductive FOTerm where
  | var : Nat → FOTerm
  | app : String → List FOTerm → FOTerm
deriving Inhabited

/-- A position is a path from the root: each step picks an argument index. -/
abbrev Pos := List Nat

/-- The subterm at a position, if the path stays inside the term. -/
def subAt : FOTerm → Pos → Option FOTerm
  | t, [] => some t
  | .app _ args, i :: p =>
      match args[i]? with
      | some s => subAt s p
      | none => none
  | .var _, _ :: _ => none

/-- Replace the subterm at a position. Off-path or invalid positions leave the term unchanged. -/
def repAt : FOTerm → Pos → FOTerm → FOTerm
  | _, [], new => new
  | .app f args, i :: p, new =>
      match args[i]? with
      | some s => .app f (args.set i (repAt s p new))
      | none => .app f args
  | t@(.var _), _ :: _, _ => t

/-- Two positions are parallel when neither is a prefix of the other (they point into independent
    subterms). -/
def Parallel (p q : Pos) : Prop := ¬ p <+: q ∧ ¬ q <+: p

/-- Reading into an application unfolds to reading the indexed argument. -/
theorem subAt_app_cons (f : String) (args : List FOTerm) (i : Nat) (p : Pos) :
    subAt (.app f args) (i :: p) = (args[i]?).bind (subAt · p) := by
  simp only [subAt]; cases args[i]? <;> rfl

/-- Replacing at an out-of-range top index leaves an application unchanged. -/
theorem repAt_invalid {f : String} {args : List FOTerm} {i : Nat} {p : Pos} {a : FOTerm}
    (h : args[i]? = none) : repAt (.app f args) (i :: p) a = .app f args := by
  simp only [repAt, h]

/-- Replacing at a valid top index sets that argument. -/
theorem repAt_valid {f : String} {args : List FOTerm} {i : Nat} {p : Pos} {a s : FOTerm}
    (h : args[i]? = some s) : repAt (.app f args) (i :: p) a = .app f (args.set i (repAt s p a)) := by
  simp only [repAt, h]

/-- A valid top index is in range. -/
theorem lt_of_getElem?_some {args : List FOTerm} {i : Nat} {s : FOTerm} (h : args[i]? = some s) :
    i < args.length := by
  rcases Nat.lt_or_ge i args.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none_iff.mpr hge] at h; simp at h

/-- Replacing inside an application at a nonempty position keeps the head symbol and the argument count. -/
theorem repAt_app_cons (f : String) (args : List FOTerm) (j : Nat) (q' : Pos) (b : FOTerm) :
    ∃ args', repAt (.app f args) (j :: q') b = .app f args' ∧ args'.length = args.length := by
  cases h : args[j]? with
  | none => exact ⟨args, repAt_invalid h, rfl⟩
  | some s => exact ⟨args.set j (repAt s q' b), repAt_valid h, List.length_set⟩

/-- A parallel pair stays parallel under a common head step. -/
theorem Parallel.tail {i : Nat} {p' q' : Pos} (h : Parallel (i :: p') (i :: q')) : Parallel p' q' :=
  ⟨fun hp => h.1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩),
   fun hq => h.2 (List.cons_prefix_cons.mpr ⟨rfl, hq⟩)⟩

/-- Reading at a position is unaffected by a replacement at a parallel position. -/
theorem subAt_repAt_parallel : ∀ {p q : Pos}, Parallel p q → ∀ (t a : FOTerm),
    subAt (repAt t p a) q = subAt t q
  | [], _, hpq, _, _ => absurd List.nil_prefix hpq.1
  | i :: p', q, hpq, t, a => by
      cases t with
      | var n => simp only [repAt]
      | app f args =>
          cases q with
          | nil => exact absurd List.nil_prefix hpq.2
          | cons j q' =>
              cases hai : args[i]? with
              | none => rw [repAt_invalid hai]
              | some s =>
                  rw [repAt_valid hai, subAt_app_cons, subAt_app_cons, List.getElem?_set]
                  by_cases hij : i = j
                  · subst hij
                    rw [if_pos rfl, if_pos (lt_of_getElem?_some hai), hai]
                    exact subAt_repAt_parallel hpq.tail s a
                  · rw [if_neg hij]

/-- Replacements at parallel positions commute. -/
theorem repAt_repAt_parallel : ∀ {p q : Pos}, Parallel p q → ∀ (t a b : FOTerm),
    repAt (repAt t p a) q b = repAt (repAt t q b) p a
  | [], _, hpq, _, _, _ => absurd List.nil_prefix hpq.1
  | i :: p', q, hpq, t, a, b => by
      cases q with
      | nil => exact absurd List.nil_prefix hpq.2
      | cons j q' =>
          cases t with
          | var n => simp only [repAt]
          | app f args =>
              by_cases hij : i = j
              · subst hij
                cases hai : args[i]? with
                | none => simp only [repAt_invalid hai]
                | some s =>
                    have hsetp : (args.set i (repAt s p' a))[i]? = some (repAt s p' a) := by
                      rw [List.getElem?_set]; simp [lt_of_getElem?_some hai]
                    have hsetq : (args.set i (repAt s q' b))[i]? = some (repAt s q' b) := by
                      rw [List.getElem?_set]; simp [lt_of_getElem?_some hai]
                    rw [repAt_valid hai, repAt_valid hai, repAt_valid hsetp, repAt_valid hsetq,
                      List.set_set, List.set_set, repAt_repAt_parallel hpq.tail s a b]
              · cases hai : args[i]? with
                | none =>
                    obtain ⟨args2, hq2, hlen⟩ := repAt_app_cons f args j q' b
                    have hi2 : args2[i]? = none := by
                      rw [List.getElem?_eq_none_iff] at hai ⊢; omega
                    rw [repAt_invalid hai, hq2, repAt_invalid hi2]
                | some s =>
                    cases haj : args[j]? with
                    | none =>
                        obtain ⟨args1, hp1, hlen1⟩ := repAt_app_cons f args i p' a
                        have hj1 : args1[j]? = none := by
                          rw [List.getElem?_eq_none_iff] at haj ⊢; omega
                        rw [repAt_invalid haj, hp1, repAt_invalid hj1]
                    | some sj =>
                        have h1 : (args.set i (repAt s p' a))[j]? = some sj := by
                          rw [List.getElem?_set_ne (by omega : i ≠ j)]; exact haj
                        have h2 : (args.set j (repAt sj q' b))[i]? = some s := by
                          rw [List.getElem?_set_ne (by omega : j ≠ i)]; exact hai
                        rw [repAt_valid hai, repAt_valid haj, repAt_valid h1, repAt_valid h2,
                          List.set_comm _ _ (by omega : i ≠ j)]

/-- Parallelism is symmetric. -/
theorem Parallel.symm {p q : Pos} (h : Parallel p q) : Parallel q p := ⟨h.2, h.1⟩

/-! ### The rewrite relation and the Parallel Moves Lemma -/

mutual
  /-- A substitution applied to a first-order term. -/
  def subst (σ : Nat → FOTerm) : FOTerm → FOTerm
    | .var x => σ x
    | .app f args => .app f (substList σ args)
  /-- A substitution applied to an argument list. -/
  def substList (σ : Nat → FOTerm) : List FOTerm → List FOTerm
    | [] => []
    | t :: ts => subst σ t :: substList σ ts
end

/-- One rewrite step of a system `R` (a list of rules): match a rule's left side at some position under
    some substitution and replace it by the instantiated right side. -/
def Rstep (R : List (FOTerm × FOTerm)) (t t' : FOTerm) : Prop :=
  ∃ (p : Pos) (l r : FOTerm) (σ : Nat → FOTerm),
    (l, r) ∈ R ∧ subAt t p = some (subst σ l) ∧ t' = repAt t p (subst σ r)

/-- The Parallel Moves Lemma: two rewrite steps at parallel (non-overlapping) positions are joinable.
    Applying each step to the other's result reaches the same term, by the position algebra. This is the
    disjoint-redex case of the Critical Pair Theorem, at the level of full term positions. -/
theorem rstep_parallel_join {R : List (FOTerm × FOTerm)} {t t1 t2 : FOTerm}
    {p q : Pos} {l1 r1 l2 r2 : FOTerm} {σ1 σ2 : Nat → FOTerm} (hpq : Parallel p q)
    (hm1 : (l1, r1) ∈ R) (hs1 : subAt t p = some (subst σ1 l1)) (ht1 : t1 = repAt t p (subst σ1 r1))
    (hm2 : (l2, r2) ∈ R) (hs2 : subAt t q = some (subst σ2 l2)) (ht2 : t2 = repAt t q (subst σ2 r2)) :
    Joinable (Rstep R) t1 t2 := by
  subst ht1 ht2
  refine ⟨repAt (repAt t p (subst σ1 r1)) q (subst σ2 r2), Relation.ReflTransGen.single ?_,
    Relation.ReflTransGen.single ?_⟩
  · exact ⟨q, l2, r2, σ2, hm2, by rw [subAt_repAt_parallel hpq]; exact hs2, rfl⟩
  · exact ⟨p, l1, r1, σ1, hm1, by rw [subAt_repAt_parallel hpq.symm]; exact hs1,
      repAt_repAt_parallel hpq t (subst σ1 r1) (subst σ2 r2)⟩

/-! ### Position composition and rewriting as a congruence

Reading and replacing compose along concatenated positions, and from that, a rewrite step performed
inside any context is itself a rewrite step (`rstep_context`). This congruence is the bridge from the
disjoint Parallel Moves case to the nested cases of the full Critical Pair Lemma. -/

/-- Reading at a concatenated position reads in two stages. -/
theorem subAt_append (t : FOTerm) (p q : Pos) :
    subAt t (p ++ q) = (subAt t p).bind (fun s => subAt s q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i p' ih =>
      cases t with
      | var n => rfl
      | app f args =>
          rw [List.cons_append, subAt_app_cons, subAt_app_cons, Option.bind_assoc]
          congr 1
          funext s
          exact ih s

/-- Reading into an application at a valid path exposes the indexed argument and the path into it. -/
theorem subAt_app_cons_some {f : String} {args : List FOTerm} {i : Nat} {p' : Pos} {s : FOTerm}
    (h : subAt (.app f args) (i :: p') = some s) : ∃ a, args[i]? = some a ∧ subAt a p' = some s := by
  rw [subAt_app_cons, Option.bind_eq_some_iff] at h
  exact h

/-- Replacing at a concatenated position replaces in two stages. -/
theorem repAt_append_of_subAt {t s : FOTerm} {p : Pos} (h : subAt t p = some s) (q : Pos) (new : FOTerm) :
    repAt t (p ++ q) new = repAt t p (repAt s q new) := by
  induction p generalizing t with
  | nil => simp only [subAt] at h; injection h with h; subst h; rfl
  | cons i p' ih =>
      cases t with
      | var n => simp [subAt] at h
      | app f args =>
          obtain ⟨a, hai, ha⟩ := subAt_app_cons_some h
          rw [List.cons_append, repAt_valid hai, repAt_valid hai, ih ha]

/-- A rewrite step inside any context is itself a rewrite step: rewriting is a congruence. -/
theorem rstep_context {R : List (FOTerm × FOTerm)} {t s s' : FOTerm} {p : Pos}
    (hsub : subAt t p = some s) (hstep : Rstep R s s') : Rstep R t (repAt t p s') := by
  obtain ⟨p0, l, r, σ, hmem, hs0, hs'⟩ := hstep
  refine ⟨p ++ p0, l, r, σ, hmem, ?_, ?_⟩
  · rw [subAt_append, hsub]; exact hs0
  · rw [hs', repAt_append_of_subAt hsub]

/-! ### Multi-step context closure

To lift a whole reduction sequence into a context (needed to reduce all copies of a variable), the
position algebra needs three more facts: reading back a fresh replacement, replacing a subterm by itself,
and collapsing two replacements at the same position. From these, a rewrite step and then a whole sequence
lift into any context. -/

/-- After replacing at a valid position, that position reads back the new subterm. -/
theorem subAt_repAt_self {t s : FOTerm} {p : Pos} (h : subAt t p = some s) (a : FOTerm) :
    subAt (repAt t p a) p = some a := by
  induction p generalizing t with
  | nil => rfl
  | cons i p' ih =>
      cases t with
      | var n => simp [subAt] at h
      | app f args =>
          obtain ⟨a0, hai, ha0⟩ := subAt_app_cons_some h
          rw [repAt_valid hai, subAt_app_cons]
          have hset : (args.set i (repAt a0 p' a))[i]? = some (repAt a0 p' a) := by
            rw [List.getElem?_set]; simp [lt_of_getElem?_some hai]
          rw [hset]; exact ih ha0

/-- Two replacements at the same position collapse to the last. -/
theorem repAt_repAt_same (t : FOTerm) (p : Pos) (a a' : FOTerm) :
    repAt (repAt t p a) p a' = repAt t p a' := by
  induction p generalizing t with
  | nil => rfl
  | cons i p' ih =>
      cases t with
      | var n => simp only [repAt]
      | app f args =>
          cases hai : args[i]? with
          | none => simp only [repAt_invalid hai]
          | some a0 =>
              have hset : (args.set i (repAt a0 p' a))[i]? = some (repAt a0 p' a) := by
                rw [List.getElem?_set]; simp [lt_of_getElem?_some hai]
              rw [repAt_valid hai, repAt_valid hset, repAt_valid hai, List.set_set, ih]

/-- A rewrite step lifts into any context regardless of what currently sits at the position. -/
theorem rstep_context_gen {R : List (FOTerm × FOTerm)} {t : FOTerm} {p : Pos} {s a a' : FOTerm}
    (h : subAt t p = some s) (hstep : Rstep R a a') : Rstep R (repAt t p a) (repAt t p a') := by
  have key := rstep_context (subAt_repAt_self h a) hstep
  rwa [repAt_repAt_same] at key

/-- A whole reduction sequence lifts into any context (at a valid position). -/
theorem rstepMany_context {R : List (FOTerm × FOTerm)} {t : FOTerm} {p : Pos} {s s' : FOTerm}
    (h : subAt t p = some s) (hsteps : Relation.ReflTransGen (Rstep R) s s') :
    Relation.ReflTransGen (Rstep R) (repAt t p s) (repAt t p s') :=
  Relation.ReflTransGen.lift (repAt t p ·) (fun _ _ hst => rstep_context_gen h hst) hsteps

/-! ### Reducing every copy of a variable

Reducing one argument of an application, then a whole argument list, then (by structural recursion) every
occurrence of a variable inside a term: if a substitution reduces at one variable, the substituted term
reduces. This is the engine of the variable-overlap case of the Critical Pair Lemma. -/

/-- Reading a single top index. -/
theorem subAt_single (f : String) (L : List FOTerm) (i : Nat) : subAt (.app f L) [i] = L[i]? := by
  rw [subAt_app_cons]; cases L[i]? <;> rfl

/-- Replacing at a single valid top index sets that argument. -/
theorem repAt_single {f : String} {L : List FOTerm} {i : Nat} (hi : i < L.length) (x : FOTerm) :
    repAt (.app f L) [i] x = .app f (L.set i x) := by
  rw [repAt_valid (List.getElem?_eq_getElem hi)]; simp [repAt]

/-- Reducing one argument of an application. -/
theorem rstepMany_setNth {R : List (FOTerm × FOTerm)} {f : String} {L : List FOTerm} {i : Nat}
    {a b : FOTerm} (hget : L[i]? = some a) (hstep : Relation.ReflTransGen (Rstep R) a b) :
    Relation.ReflTransGen (Rstep R) (.app f L) (.app f (L.set i b)) := by
  have hi : i < L.length := lt_of_getElem?_some hget
  have hsub : subAt (.app f L) [i] = some a := by rw [subAt_single]; exact hget
  have key := rstepMany_context hsub hstep
  rw [repAt_single hi, repAt_single hi] at key
  have hself : L.set i a = L := by
    have hia : L[i] = a := by rw [List.getElem?_eq_getElem hi] at hget; injection hget
    rw [← hia]; exact List.set_getElem_self hi
  rwa [hself] at key

/-- Reducing every argument of an application, pointwise. -/
theorem rstepMany_app_from {R : List (FOTerm × FOTerm)} {f : String} {L L' : List FOTerm}
    (h : List.Forall₂ (Relation.ReflTransGen (Rstep R)) L L') (pre : List FOTerm) :
    Relation.ReflTransGen (Rstep R) (.app f (pre ++ L)) (.app f (pre ++ L')) := by
  induction h generalizing pre with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a a' L L' hab _ ih =>
      have hget : (pre ++ a :: L)[pre.length]? = some a := by
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      have hset : (pre ++ a :: L).set pre.length a' = pre ++ a' :: L := by
        rw [List.set_append]; simp
      have step1 := rstepMany_setNth (f := f) hget hab
      rw [hset] at step1
      have step2 := ih (pre ++ [a'])
      simp only [List.append_assoc, List.singleton_append] at step2
      exact step1.trans step2

mutual
  /-- Reduce-all-copies: if a substitution reduces at one variable, the substituted term reduces. -/
  theorem subst_reduces {R : List (FOTerm × FOTerm)} {x : Nat} {σ σ' : Nat → FOTerm}
      (hagree : ∀ y, y ≠ x → σ y = σ' y) (hx : Relation.ReflTransGen (Rstep R) (σ x) (σ' x)) :
      ∀ r, Relation.ReflTransGen (Rstep R) (subst σ r) (subst σ' r)
    | .var y => by
        by_cases h : y = x
        · subst h; simp only [subst]; exact hx
        · simp only [subst, hagree y h]; exact Relation.ReflTransGen.refl
    | .app f args => by
        simp only [subst]
        have key := rstepMany_app_from (f := f) (substList_forall hagree hx args) []
        simpa using key
  /-- The argument-list version of reduce-all-copies. -/
  theorem substList_forall {R : List (FOTerm × FOTerm)} {x : Nat} {σ σ' : Nat → FOTerm}
      (hagree : ∀ y, y ≠ x → σ y = σ' y) (hx : Relation.ReflTransGen (Rstep R) (σ x) (σ' x)) :
      ∀ args, List.Forall₂ (Relation.ReflTransGen (Rstep R)) (substList σ args) (substList σ' args)
    | [] => by simp only [substList]; exact .nil
    | a :: as => by
        simp only [substList]
        exact .cons (subst_reduces hagree hx a) (substList_forall hagree hx as)
end

/-! ### The variable-overlap case of the Critical Pair Theorem (Case 2.1)

When two steps from the same redex `l·σ` are the rule contraction (giving `r·σ`) and a reduction inside
the image of a variable (giving `r·σ'` after replacing `σ` by `σ'` at that variable, which for a
left-linear rule is one step), the peak is joinable: the contractum `r·σ` reduces all copies of the
variable down to `r·σ'` (reduce-all-copies), and `l·σ'` contracts to `r·σ'` by re-applying the rule. So a
nested overlap below a variable never breaks local confluence. -/

/-- The variable-overlap peak `r·σ ← l·σ → l·σ'` (reduction below a variable) is joinable. -/
theorem localConfluence_variable {R : List (FOTerm × FOTerm)} {x : Nat} {σ σ' : Nat → FOTerm}
    {l1 r1 : FOTerm} (hmem : (l1, r1) ∈ R) (hagree : ∀ y, y ≠ x → σ y = σ' y)
    (hx : Relation.ReflTransGen (Rstep R) (σ x) (σ' x)) :
    Joinable (Rstep R) (subst σ r1) (subst σ' l1) :=
  ⟨subst σ' r1, subst_reduces hagree hx r1,
    Relation.ReflTransGen.single ⟨[], l1, r1, σ', hmem, rfl, rfl⟩⟩

/-- A worked variable-overlap peak: with `f(x) -> g(x)` and `b -> c`, the term `f(b)` reduces to `g(b)`
    (the rule) and to `f(c)` (the variable's image), and these join (at `g(c)`). -/
def vsys : List (FOTerm × FOTerm) :=
  [(.app "f" [.var 0], .app "g" [.var 0]), (.app "b" [], .app "c" [])]

theorem var_overlap_join :
    Joinable (Rstep vsys) (.app "g" [.app "b" []]) (.app "f" [.app "c" []]) := by
  have hbc : Rstep vsys (.app "b" []) (.app "c" []) :=
    ⟨[], .app "b" [], .app "c" [], (fun _ => .app "b" []), .tail _ (.head _), rfl, rfl⟩
  have key := localConfluence_variable (R := vsys) (x := 0)
    (σ := fun n => if n = 0 then .app "b" [] else .var n)
    (σ' := fun n => if n = 0 then .app "c" [] else .var n)
    (l1 := .app "f" [.var 0]) (r1 := .app "g" [.var 0])
    (.head _) (fun y h => by simp [h]) (Relation.ReflTransGen.single hbc)
  simpa [subst, substList] using key

/-! ### Positions of a substituted term (the gateway to the critical-pair case)

A position inside `subst σ l` either stays within the pattern `l` (and reads a substituted subterm of
`l`) or runs past a variable of `l` into that variable's image. This decomposition is what lets the
nested-overlap dispatch separate the variable case (Case 2.1) from the genuine critical-pair case
(Case 2.2). -/

/-- Indexing commutes with list substitution. -/
theorem substList_getElem (σ : Nat → FOTerm) :
    ∀ (args : List FOTerm) (i : Nat), (substList σ args)[i]? = (args[i]?).map (subst σ)
  | [], _ => by simp [substList]
  | _ :: _, 0 => by simp [substList]
  | _ :: as, i + 1 => by simp only [substList, List.getElem?_cons_succ]; exact substList_getElem σ as i

/-- The positions-of-a-substitution decomposition. -/
theorem subAt_subst_dichotomy (σ : Nat → FOTerm) :
    ∀ (l : FOTerm) (o : Pos) {w : FOTerm}, subAt (subst σ l) o = some w →
      (∃ lo, subAt l o = some lo ∧ w = subst σ lo) ∨
      (∃ ov x q, subAt l ov = some (.var x) ∧ o = ov ++ q ∧ subAt (σ x) q = some w)
  | l, [], w, h => by
      simp only [subAt] at h; injection h with h
      exact Or.inl ⟨l, rfl, h.symm⟩
  | .var x, i :: o', w, h => by
      refine Or.inr ⟨[], x, i :: o', rfl, rfl, ?_⟩
      simpa only [subst] using h
  | .app f args, i :: o', w, h => by
      rw [subst, subAt_app_cons, substList_getElem] at h
      cases hai : args[i]? with
      | none => rw [hai] at h; simp at h
      | some a =>
          rw [hai] at h
          rcases subAt_subst_dichotomy σ a o' h with ⟨lo, hlo, hw⟩ | ⟨ov, x, q, hov, hoq, hq⟩
          · refine Or.inl ⟨lo, ?_, hw⟩
            rw [subAt_app_cons, hai]; exact hlo
          · refine Or.inr ⟨i :: ov, x, q, ?_, ?_, hq⟩
            · rw [subAt_app_cons, hai]; exact hov
            · rw [hoq]; rfl

/-! ### Substitution insensitive to an absent variable

For the variable-overlap dispatch we also need that updating a substitution at a variable that does not
occur in a term leaves the term's instance unchanged. `notInVar x t` says `x` is absent from `t`. -/

mutual
  /-- `x` does not occur as a variable anywhere in the term. -/
  def notInVar (x : Nat) : FOTerm → Prop
    | .var y => y ≠ x
    | .app _ args => notInVarList x args
  /-- `x` does not occur in any term of the list. -/
  def notInVarList (x : Nat) : List FOTerm → Prop
    | [] => True
    | a :: as => notInVar x a ∧ notInVarList x as
end

mutual
  /-- Updating a substitution at an absent variable does not change the instance. -/
  theorem subst_update_notIn {x : Nat} {σ : Nat → FOTerm} {v : FOTerm} :
      ∀ {t : FOTerm}, notInVar x t → subst (Function.update σ x v) t = subst σ t
    | .var y, h => by
        simp only [notInVar] at h
        simp only [subst, Function.update_apply, if_neg h]
    | .app f args, h => by
        simp only [notInVar] at h
        simp only [subst, substList_update_notIn h]
  /-- The list version. -/
  theorem substList_update_notIn {x : Nat} {σ : Nat → FOTerm} {v : FOTerm} :
      ∀ {args : List FOTerm}, notInVarList x args →
        substList (Function.update σ x v) args = substList σ args
    | [], _ => rfl
    | _ :: _, h => by
        simp only [notInVarList] at h
        simp only [substList, subst_update_notIn h.1, substList_update_notIn h.2]
end

/-! ### Updating a uniquely-occurring variable equals replacing at its position

`occOnlyAt x l ov` says `x` occurs in `l` only at position `ov` (a left-linearity condition for `x`).
Then updating the substitution at `x` is the same as replacing the subterm of `l·σ` at `ov`. -/

mutual
  /-- `x` occurs in the term only at position `ov`. -/
  def occOnlyAt (x : Nat) : FOTerm → Pos → Prop
    | .var y, ov => y = x ∧ ov = []
    | .app _ _, [] => False
    | .app _ args, i :: ov' => occOnlyAtList x args i ov'
  /-- `x` occurs in the list only in element `i`, there only at `ov'`. -/
  def occOnlyAtList (x : Nat) : List FOTerm → Nat → Pos → Prop
    | [], _, _ => False
    | a :: as, 0, ov' => occOnlyAt x a ov' ∧ notInVarList x as
    | a :: as, i + 1, ov' => notInVar x a ∧ occOnlyAtList x as i ov'
end

mutual
  /-- Updating at a uniquely-occurring variable equals replacing the subterm at its position. -/
  theorem subst_update_eq_repAt {x : Nat} {σ : Nat → FOTerm} {w : FOTerm} :
      ∀ {l : FOTerm} {ov : Pos}, occOnlyAt x l ov →
        subst (Function.update σ x w) l = repAt (subst σ l) ov w
    | .var _, _, h => by
        simp only [occOnlyAt] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [subst, repAt]
    | .app _ _, [], h => by simp only [occOnlyAt] at h
    | .app f args, _ :: _, h => by
        simp only [occOnlyAt] at h
        obtain ⟨s, hs, heq⟩ := substList_update_eq_setNth h
        simp only [subst]
        rw [heq, repAt_valid hs]
  /-- The list version: updating sets exactly the one argument that contains the variable. -/
  theorem substList_update_eq_setNth {x : Nat} {σ : Nat → FOTerm} {w : FOTerm} :
      ∀ {args : List FOTerm} {i : Nat} {ov' : Pos}, occOnlyAtList x args i ov' →
        ∃ s, (substList σ args)[i]? = some s ∧
          substList (Function.update σ x w) args = (substList σ args).set i (repAt s ov' w)
    | [], _, _, h => by simp only [occOnlyAtList] at h
    | a :: as, 0, ov', h => by
        simp only [occOnlyAtList] at h
        refine ⟨subst σ a, by simp [substList], ?_⟩
        simp only [substList, subst_update_eq_repAt h.1, substList_update_notIn h.2, List.set]
    | a :: as, i + 1, ov', h => by
        simp only [occOnlyAtList] at h
        obtain ⟨s, hs, heq⟩ := substList_update_eq_setNth (σ := σ) (w := w) h.2
        refine ⟨s, by simp [substList, hs], ?_⟩
        simp only [substList, subst_update_notIn h.1, heq, List.set]
end

/-! ### Assembling local confluence from the three cases

Three small bridges, then the dispatch: any two positions are parallel or one is a prefix of the other;
joinability lifts into a context; and `subAt` commutes with `subst` at a position that stays within the
pattern. -/

/-- Any two positions are parallel, or one is a prefix of the other. -/
theorem pos_trichotomy (p q : Pos) : Parallel p q ∨ p <+: q ∨ q <+: p := by
  by_cases h1 : p <+: q
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : q <+: p
    · exact Or.inr (Or.inr h2)
    · exact Or.inl ⟨h1, h2⟩

/-- Joinability lifts into any context (at a valid position). -/
theorem joinable_context {R : List (FOTerm × FOTerm)} {t : FOTerm} {p : Pos} {s a b : FOTerm}
    (h : subAt t p = some s) (hab : Joinable (Rstep R) a b) :
    Joinable (Rstep R) (repAt t p a) (repAt t p b) := by
  obtain ⟨c, hac, hbc⟩ := hab
  refine ⟨repAt t p c, ?_, ?_⟩
  · have key := rstepMany_context (subAt_repAt_self h a) hac
    rwa [repAt_repAt_same, repAt_repAt_same] at key
  · have key := rstepMany_context (subAt_repAt_self h b) hbc
    rwa [repAt_repAt_same, repAt_repAt_same] at key

/-- `subAt` commutes with `subst` at a position staying within the pattern. -/
theorem subAt_subst_within {σ : Nat → FOTerm} :
    ∀ {l : FOTerm} {ov : Pos} {lo : FOTerm}, subAt l ov = some lo →
      subAt (subst σ l) ov = some (subst σ lo)
  | _, [], _, h => by simp only [subAt] at h ⊢; injection h with h; rw [h]
  | .var _, _ :: _, _, h => by simp [subAt] at h
  | .app f args, i :: ov', lo, h => by
      obtain ⟨a, hai, ha⟩ := subAt_app_cons_some h
      rw [subst, subAt_app_cons, substList_getElem, hai]
      simpa using subAt_subst_within (l := a) ha

/-- Left-linearity: in every rule's left side, each variable occurs only at its position. -/
def LeftLinear (R : List (FOTerm × FOTerm)) : Prop :=
  ∀ l r, (l, r) ∈ R → ∀ ov x, subAt l ov = some (.var x) → occOnlyAt x l ov

/-- Critical pairs joinable: every non-variable overlap of two rules gives a joinable peak. This is the
    hypothesis of the Critical Pair Theorem (here with the actual overlapping substitutions, the abstract
    critical-pair formulation, so no separate unification machinery is needed). -/
def CPJ (R : List (FOTerm × FOTerm)) : Prop :=
  ∀ l1 r1 l2 r2 (o : Pos) lo θ1 θ2, (l1, r1) ∈ R → (l2, r2) ∈ R →
    subAt l1 o = some lo → (∀ y, lo ≠ .var y) → subst θ1 lo = subst θ2 l2 →
    Joinable (Rstep R) (subst θ1 r1) (repAt (subst θ1 l1) o (subst θ2 r2))

/-- Joinability is symmetric (the relation-generic `Joinable.symm`, specialized to `Rstep`). -/
theorem joinable_symm {R : List (FOTerm × FOTerm)} {a b : FOTerm}
    (h : Joinable (Rstep R) a b) : Joinable (Rstep R) b a := h.symm

/-- The variable-overlap case from an actual nested peak: the inner redex sits inside the image of a
    variable of the outer rule, at position `ov ++ q`. Left-linearity makes the inner step turn `l1·θ1`
    into `l1·θ1'`, and reduce-all-copies turns `r1·θ1` into `r1·θ1'`. -/
theorem localConfluence_var_case {R : List (FOTerm × FOTerm)} (hll : LeftLinear R)
    {l1 r1 l2 r2 : FOTerm} {θ1 θ2 : Nat → FOTerm} {ov : Pos} {x : Nat} {q : Pos}
    (hm1 : (l1, r1) ∈ R) (hm2 : (l2, r2) ∈ R) (hov : subAt l1 ov = some (.var x))
    (hq : subAt (θ1 x) q = some (subst θ2 l2)) :
    Joinable (Rstep R) (subst θ1 r1) (repAt (subst θ1 l1) (ov ++ q) (subst θ2 r2)) := by
  have hocc : occOnlyAt x l1 ov := hll l1 r1 hm1 ov x hov
  have hrule2 : Rstep R (subst θ2 l2) (subst θ2 r2) := ⟨[], l2, r2, θ2, hm2, rfl, rfl⟩
  have hinner : Rstep R (θ1 x) (repAt (θ1 x) q (subst θ2 r2)) := rstep_context hq hrule2
  have hjoin :=
    localConfluence_variable (σ := θ1) (σ' := Function.update θ1 x (repAt (θ1 x) q (subst θ2 r2)))
      hm1 (fun y hy => by rw [Function.update_apply, if_neg hy])
      (by simpa using Relation.ReflTransGen.single hinner)
  have heq : repAt (subst θ1 l1) (ov ++ q) (subst θ2 r2)
      = subst (Function.update θ1 x (repAt (θ1 x) q (subst θ2 r2))) l1 := by
    rw [repAt_append_of_subAt (subAt_subst_within hov),
        show subst θ1 (FOTerm.var x) = θ1 x from rfl, ← subst_update_eq_repAt hocc]
  rw [heq]; exact hjoin

/-- The nested-overlap dispatch: when one redex is inside the other, the peak is joinable by the
    variable case (overlap below a variable) or the critical-pair hypothesis (non-variable overlap). -/
theorem localConfluence_nested {R : List (FOTerm × FOTerm)} (hll : LeftLinear R) (hcpj : CPJ R)
    {t : FOTerm} {p1 o : Pos} {l1 r1 l2 r2 : FOTerm} {θ1 θ2 : Nat → FOTerm}
    (hm1 : (l1, r1) ∈ R) (hs1 : subAt t p1 = some (subst θ1 l1))
    (hm2 : (l2, r2) ∈ R) (hs2 : subAt t (p1 ++ o) = some (subst θ2 l2)) :
    Joinable (Rstep R) (repAt t p1 (subst θ1 r1)) (repAt t (p1 ++ o) (subst θ2 r2)) := by
  have hsub : subAt (subst θ1 l1) o = some (subst θ2 l2) := by
    rw [subAt_append, hs1] at hs2; simpa using hs2
  rw [repAt_append_of_subAt hs1]
  apply joinable_context hs1
  rcases subAt_subst_dichotomy θ1 l1 o hsub with ⟨lo, hlo, hw⟩ | ⟨ov, x, q, hov, hoq, hq⟩
  · cases lo with
    | var x =>
        have hqx : subAt (θ1 x) [] = some (subst θ2 l2) := by
          simp only [subAt]; exact congrArg some hw.symm
        have := localConfluence_var_case hll hm1 hm2 hlo hqx
        simpa using this
    | app g largs =>
        exact hcpj l1 r1 l2 r2 o (.app g largs) θ1 θ2 hm1 hm2 hlo (by simp) hw.symm
  · rw [hoq]
    exact localConfluence_var_case hll hm1 hm2 hov hq

/-- The Critical Pair Theorem (soundness, left-linear): if all critical pairs are joinable, the rewrite
    relation is locally confluent. The three cases (disjoint, variable overlap, critical pair) are
    dispatched by the position trichotomy. -/
theorem localConfluent_of_CPJ {R : List (FOTerm × FOTerm)} (hll : LeftLinear R) (hcpj : CPJ R) :
    LocallyConfluent (Rstep R) := by
  intro t t1 t2 h1 h2
  obtain ⟨p1, l1, r1, θ1, hm1, hs1, rfl⟩ := h1
  obtain ⟨p2, l2, r2, θ2, hm2, hs2, rfl⟩ := h2
  rcases pos_trichotomy p1 p2 with hpar | ⟨o, rfl⟩ | ⟨o, rfl⟩
  · exact rstep_parallel_join hpar hm1 hs1 rfl hm2 hs2 rfl
  · exact localConfluence_nested hll hcpj hm1 hs1 hm2 hs2
  · exact joinable_symm (localConfluence_nested hll hcpj hm2 hs2 hm1 hs1)

/-- The soundness half of the Knuth-Bendix-Huet criterion: a terminating, left-linear system whose critical
    pairs are joinable is confluent. Local confluence comes from the Critical Pair Theorem, confluence from
    Newman's lemma. Joinability of the critical pairs (`CPJ`) is assumed here, not decided; computing the
    finitely many critical pairs by unification (to discharge `CPJ` automatically) is future work. -/
theorem confluent_of_CPJ {R : List (FOTerm × FOTerm)} (hll : LeftLinear R) (hcpj : CPJ R)
    (hwf : WellFounded (fun b a => Rstep R a b)) : Confluent (Rstep R) :=
  newman (Rstep R) hwf (localConfluent_of_CPJ hll hcpj)

/-! ### A worked instance: two parallel redexes join

With the single rule `f(x) -> x`, the term `g(f(a), f(b))` has two redexes at the parallel positions
`[0]` and `[1]`. The Parallel Moves Lemma joins them: both reach `g(a, b)`. -/

/-- The system with the single projection rule `f(x) -> x`. -/
def projSys : List (FOTerm × FOTerm) := [(.app "f" [.var 0], .var 0)]

theorem proj_parallel_join :
    Joinable (Rstep projSys)
      (.app "g" [.app "a" [], .app "f" [.app "b" []]])
      (.app "g" [.app "f" [.app "a" []], .app "b" []]) :=
  rstep_parallel_join (t := .app "g" [.app "f" [.app "a" []], .app "f" [.app "b" []]])
    (p := [0]) (q := [1]) (l1 := .app "f" [.var 0]) (r1 := .var 0)
    (l2 := .app "f" [.var 0]) (r2 := .var 0)
    (σ1 := fun _ => .app "a" []) (σ2 := fun _ => .app "b" [])
    ⟨by decide, by decide⟩
    (by simp [projSys]) rfl rfl
    (by simp [projSys]) rfl rfl

/-! ### A worked instance of the Critical Pair Theorem itself

The projection system `f(x) -> x` is left-linear and its only non-variable overlap (the root self-overlap)
is trivially joinable, so it satisfies the hypotheses of `localConfluent_of_CPJ`, which then yields a
genuine local-confluence theorem. This witnesses that the Critical Pair Theorem is not vacuous. -/

/-- `f(x) -> x` is left-linear: its single variable occurs once. -/
theorem leftLinear_projSys : LeftLinear projSys := by
  intro l r hm ov x hsub
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  cases ov with
  | nil => simp [subAt] at hsub
  | cons i ov' =>
      cases i with
      | zero =>
          cases ov' with
          | nil =>
              simp only [subAt_single, List.getElem?_cons_zero, Option.some.injEq] at hsub
              obtain ⟨rfl⟩ := hsub
              exact ⟨⟨rfl, rfl⟩, trivial⟩
          | cons _ _ => simp [subAt] at hsub
      | succ j => simp [subAt] at hsub

/-- `f(x) -> x` has joinable critical pairs: its only non-variable overlap forces the two sides equal. -/
theorem cpj_projSys : CPJ projSys := by
  intro l1 r1 l2 r2 o lo θ1 θ2 hm1 hm2 hsub hnv hov
  simp only [projSys, List.mem_singleton, Prod.mk.injEq] at hm1 hm2
  obtain ⟨rfl, rfl⟩ := hm1
  obtain ⟨rfl, rfl⟩ := hm2
  cases o with
  | nil =>
      simp only [subAt, Option.some.injEq] at hsub
      subst hsub
      simp only [subst, substList] at hov
      injection hov with _ hov
      injection hov with hov _
      refine ⟨θ1 0, Relation.ReflTransGen.refl, ?_⟩
      simp only [subst, repAt]
      rw [hov]
  | cons i o' =>
      exfalso
      cases i with
      | zero =>
          cases o' with
          | nil =>
              simp only [subAt_single, List.getElem?_cons_zero, Option.some.injEq] at hsub
              exact hnv 0 hsub.symm
          | cons _ _ => simp [subAt] at hsub
      | succ j => simp [subAt] at hsub

/-- The Critical Pair Theorem instantiated: `f(x) -> x` is locally confluent. -/
theorem localConfluent_projSys : LocallyConfluent (Rstep projSys) :=
  localConfluent_of_CPJ leftLinear_projSys cpj_projSys

end MeTTaIL.CP
