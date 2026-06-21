/-
Module: MeTTaILProofs.CPDecide
Layer: Proofs
Purpose: Wire the verified unifier (`Unify`) into the abstract critical-pair condition `CPJ` (in
  `CriticalPairs`), turning it into an effective syntactic check. The foundation here is that first-order
  rewriting is stable under substitution: a rewrite step (and joinability) is preserved when an arbitrary
  substitution is applied. This is what lets the critical-pair peak, computed at the most general unifier,
  represent every concrete overlap (which is a substitution instance of it).
Imports: MeTTaILProofs.Unify (substComp, subst_comp), MeTTaILProofs.CriticalPairs (Rstep, subAt, repAt)
Trusted boundary: none (fully proved)
Main exports: subAt_subst, repAt_subst, rstep_subst, rstepMany_subst, joinable_subst
Open obligations: the variable-disjoint renaming and the final representative lemma
  (criticalPairsJoinable -> CPJ) build on these.
-/
import MeTTaILProofs.Unify

namespace MeTTaIL.CP

/-- Substitution commutes with list update. -/
theorem substList_set (ρ : Nat → FOTerm) :
    ∀ (args : List FOTerm) (i : Nat) (x : FOTerm),
      substList ρ (args.set i x) = (substList ρ args).set i (subst ρ x)
  | [], _, _ => rfl
  | _ :: _, 0, _ => by simp only [List.set_cons_zero, substList]
  | a :: as, i + 1, x => by simp only [List.set_cons_succ, substList]; rw [substList_set ρ as i x]

/-- Reading a position commutes with substitution. -/
theorem subAt_subst (ρ : Nat → FOTerm) : ∀ {s : FOTerm} {p : Pos} {w : FOTerm},
    subAt s p = some w → subAt (subst ρ s) p = some (subst ρ w)
  | s, [], w, h => by simp only [subAt, Option.some.injEq] at h; subst h; rfl
  | .var _, _ :: _, _, h => by simp [subAt] at h
  | .app f args, i :: p, w, h => by
      simp only [subAt] at h
      split at h
      · rename_i a hai
        simp only [subst, subAt, substList_getElem, hai, Option.map_some]
        exact subAt_subst ρ h
      · simp at h

/-- Replacing at a valid position commutes with substitution. -/
theorem repAt_subst (ρ : Nat → FOTerm) : ∀ {s : FOTerm} {p : Pos} {u : FOTerm} (w : FOTerm),
    subAt s p = some u → repAt (subst ρ s) p (subst ρ w) = subst ρ (repAt s p w)
  | _, [], _, _, _ => rfl
  | .var _, _ :: _, _, _, h => by simp [subAt] at h
  | .app f args, i :: p, u, w, h => by
      simp only [subAt] at h
      split at h
      · rename_i a hai
        simp only [subst, repAt, substList_getElem, hai, Option.map_some, substList_set]
        rw [repAt_subst ρ w h]
      · simp at h

/-- First-order rewriting is stable under substitution: a step persists when any substitution is applied. -/
theorem rstep_subst {R : List (FOTerm × FOTerm)} (ρ : Nat → FOTerm) {s s' : FOTerm}
    (h : Rstep R s s') : Rstep R (subst ρ s) (subst ρ s') := by
  obtain ⟨p, l, r, σ, hmem, hsub, hrep⟩ := h
  refine ⟨p, l, r, substComp ρ σ, hmem, ?_, ?_⟩
  · rw [← subst_comp]; exact subAt_subst ρ hsub
  · subst hrep
    rw [← subst_comp]
    exact (repAt_subst ρ (subst σ r) hsub).symm

/-- Many-step rewriting is stable under substitution. -/
theorem rstepMany_subst {R : List (FOTerm × FOTerm)} (ρ : Nat → FOTerm) {s s' : FOTerm}
    (h : Relation.ReflTransGen (Rstep R) s s') :
    Relation.ReflTransGen (Rstep R) (subst ρ s) (subst ρ s') :=
  Relation.ReflTransGen.lift (subst ρ) (fun _ _ hab => rstep_subst ρ hab) h

/-- Joinability is closed under substitution. -/
theorem joinable_subst {R : List (FOTerm × FOTerm)} (ρ : Nat → FOTerm) {a b : FOTerm}
    (h : Joinable (Rstep R) a b) : Joinable (Rstep R) (subst ρ a) (subst ρ b) := by
  obtain ⟨c, hac, hbc⟩ := h
  exact ⟨subst ρ c, rstepMany_subst ρ hac, rstepMany_subst ρ hbc⟩

/-! ### Variable-disjoint renaming, for overlapping a rule with (a copy of) another -/

mutual
  /-- Shift every variable by `k`, to make one rule's variables disjoint from another's. -/
  def shift (k : Nat) : FOTerm → FOTerm
    | .var n => .var (n + k)
    | .app f args => .app f (shiftList k args)
  def shiftList (k : Nat) : List FOTerm → List FOTerm
    | [] => []
    | a :: as => shift k a :: shiftList k as
end

mutual
  /-- Substituting a shifted term is substituting under the shifted substitution. -/
  theorem subst_shift (Θ : Nat → FOTerm) (k : Nat) :
      ∀ t : FOTerm, subst Θ (shift k t) = subst (fun m => Θ (m + k)) t
    | .var _ => rfl
    | .app _ args => by simp only [shift, subst]; rw [substList_shift Θ k args]
  theorem substList_shift (Θ : Nat → FOTerm) (k : Nat) :
      ∀ args : List FOTerm, substList Θ (shiftList k args) = substList (fun m => Θ (m + k)) args
    | [] => rfl
    | a :: as => by simp only [shiftList, substList]; rw [subst_shift Θ k a, substList_shift Θ k as]
end

mutual
  /-- Substitution depends only on the substitution's values on the term's variables. -/
  theorem subst_vars_agree {σ1 σ2 : Nat → FOTerm} :
      ∀ {t : FOTerm}, (∀ n ∈ varsFin t, σ1 n = σ2 n) → subst σ1 t = subst σ2 t
    | .var n, h => h n (by simp [varsFin])
    | .app _ args, h => by simp only [subst]; rw [substList_vars_agree (by simpa [varsFin] using h)]
  theorem substList_vars_agree {σ1 σ2 : Nat → FOTerm} :
      ∀ {args : List FOTerm}, (∀ n ∈ varsFinList args, σ1 n = σ2 n) →
        substList σ1 args = substList σ2 args
    | [], _ => rfl
    | a :: as, h => by
        simp only [substList]
        rw [subst_vars_agree (fun n hn => h n (by simp [varsFinList, hn])),
          substList_vars_agree (fun n hn => h n (by simp [varsFinList, hn]))]
end

/-- A list element's variables are among the list's. -/
theorem varsFin_mem_subset : ∀ {a : FOTerm} {args : List FOTerm}, a ∈ args → varsFin a ⊆ varsFinList args
  | _, b :: bs, h => by
      simp only [varsFinList]
      rcases List.mem_cons.mp h with rfl | h
      · exact Finset.subset_union_left
      · exact (varsFin_mem_subset h).trans Finset.subset_union_right

/-- A subterm's variables are among the whole term's. -/
theorem subAt_varsFin_subset : ∀ {t : FOTerm} {o : Pos} {w : FOTerm},
    subAt t o = some w → varsFin w ⊆ varsFin t
  | _, [], _, h => by simp only [subAt, Option.some.injEq] at h; subst h; exact Finset.Subset.refl _
  | .var _, _ :: _, _, h => by simp [subAt] at h
  | .app f args, i :: p, w, h => by
      simp only [subAt] at h
      split at h
      · rename_i a hai
        refine (subAt_varsFin_subset h).trans ?_
        simp only [varsFin]
        exact varsFin_mem_subset (List.mem_of_getElem? hai)
      · simp at h

/-- A bound strictly above all of a term's variables. -/
def bound (t : FOTerm) : Nat := (varsFin t).sup id + 1

theorem lt_bound {t : FOTerm} {n : Nat} (hn : n ∈ varsFin t) : n < bound t :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)

/-- The critical-pair joinability check for one overlap: whenever the overlap of rule 1 (at position `o`,
    subterm `lo`) with a variable-disjoint copy of rule 2 unifies, the resulting critical pair is joinable. -/
def CPCheck (R : List (FOTerm × FOTerm)) (l1 r1 l2 r2 : FOTerm) (o : Pos) (lo : FOTerm) : Prop :=
  ∀ (f : Nat) (σ : Nat → FOTerm), unify f [(lo, shift (bound l1) l2)] = some σ →
    Joinable (Rstep R) (subst σ r1) (repAt (subst σ l1) o (subst σ (shift (bound l1) r2)))

/-- The representative lemma: a concrete overlap of two rules is joinable provided the critical pair
    computed at the most general unifier (of `lo` with a variable-disjoint copy of `l2`) is joinable. The
    concrete overlap is a substitution instance of the most-general critical pair, and joinability is closed
    under substitution. This is the heart of turning the abstract `CPJ` into an effective syntactic check. -/
theorem cpj_overlap {R : List (FOTerm × FOTerm)} {l1 r1 l2 r2 lo : FOTerm} {o : Pos}
    {θ1 θ2 : Nat → FOTerm}
    (hvr1 : ∀ n ∈ varsFin r1, n ∈ varsFin l1)
    (ho : subAt l1 o = some lo)
    (hov : subst θ1 lo = subst θ2 l2)
    (hcheck : CPCheck R l1 r1 l2 r2 o lo) :
    Joinable (Rstep R) (subst θ1 r1) (repAt (subst θ1 l1) o (subst θ2 r2)) := by
  set Θ : Nat → FOTerm := fun n => if n < bound l1 then θ1 n else θ2 (n - bound l1) with hΘ
  have hΘlt : ∀ {t : FOTerm}, (∀ n ∈ varsFin t, n < bound l1) → subst Θ t = subst θ1 t := by
    intro t ht; exact subst_vars_agree (fun n hn => by simp only [hΘ, if_pos (ht n hn)])
  have hl1 : subst Θ l1 = subst θ1 l1 := hΘlt (fun _ hn => lt_bound hn)
  have hlo : subst Θ lo = subst θ1 lo := hΘlt (fun _ hn => lt_bound (subAt_varsFin_subset ho hn))
  have hr1 : subst Θ r1 = subst θ1 r1 := hΘlt (fun n hn => lt_bound (hvr1 n hn))
  have hshift : ∀ t : FOTerm, subst Θ (shift (bound l1) t) = subst θ2 t := by
    intro t; rw [subst_shift]
    apply subst_vars_agree
    intro n _
    show Θ (n + bound l1) = θ2 n
    simp only [hΘ, if_neg (Nat.not_lt.mpr (Nat.le_add_left (bound l1) n)), Nat.add_sub_cancel]
  have hUnifies : Unifies Θ [(lo, shift (bound l1) l2)] := by
    intro e he; simp only [List.mem_singleton] at he; subst he
    show subst Θ lo = subst Θ (shift (bound l1) l2)
    rw [hlo, hshift]; exact hov
  obtain ⟨f, σ, hf⟩ := unify_complete _ Θ hUnifies
  obtain ⟨ρ, hρ⟩ := unify_mgu f _ σ Θ hf hUnifies
  have hΘeq : ∀ t, subst ρ (subst σ t) = subst Θ t := fun t => by
    rw [subst_comp]; exact subst_funext (fun n => (hρ n).symm) t
  have hlift := joinable_subst ρ (hcheck f σ hf)
  rw [hΘeq r1] at hlift
  rw [← repAt_subst ρ (subst σ (shift (bound l1) r2)) (subAt_subst σ ho)] at hlift
  rw [hΘeq l1, hΘeq (shift (bound l1) r2), hr1, hl1, hshift r2] at hlift
  exact hlift

/-- The effective Critical Pair criterion: `CPJ` (the hypothesis of the Critical Pair Theorem) follows from
    a syntactic check over the unify-computed critical pairs. For every pair of rules and every position, if
    unifying the overlap (against a variable-disjoint copy of the second rule) succeeds, the resulting
    critical pair must be joinable. This turns the abstract `CPJ` into an effective, decidable-modulo-
    joinability check, the Knuth-Bendix-Huet criterion. Combined with `confluent_of_CPJ` (left-linear +
    terminating) it certifies confluence, and via the `CPRuntime` bridge, runtime confluence. This closes
    the compromise that `CPJ` was assumed rather than decided. -/
theorem CPJ_of_check {R : List (FOTerm × FOTerm)}
    (hvars : ∀ l r, (l, r) ∈ R → ∀ n ∈ varsFin r, n ∈ varsFin l)
    (hcheck : ∀ l1 r1 l2 r2, (l1, r1) ∈ R → (l2, r2) ∈ R → ∀ (o : Pos) (lo : FOTerm),
        subAt l1 o = some lo → CPCheck R l1 r1 l2 r2 o lo) :
    CPJ R := by
  intro l1 r1 l2 r2 o lo θ1 θ2 hm1 hm2 ho _ hov
  exact cpj_overlap (hvars l1 r1 hm1) ho hov (hcheck l1 r1 l2 r2 hm1 hm2 o lo ho)

end MeTTaIL.CP
