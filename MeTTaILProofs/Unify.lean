/-
Module: MeTTaILProofs.Unify
Layer: Proofs
Purpose: First-order syntactic unification over `FOTerm`, the decision procedure behind critical pairs. This
  is the computational layer that compromise #3 needs: it lets the abstract critical-pair condition `CPJ`
  (in `CriticalPairs`) be turned into an effective syntactic check, by unifying the left-hand sides of two
  rules at a non-variable position. This file builds the algorithm (Robinson / Martelli-Montanari, applying
  bindings eagerly with substitution composition) and proves it sound: a returned substitution really does
  unify every input equation. Completeness and most-generality, and the critical-pair construction on top,
  follow in later steps.
Imports: MeTTaILProofs.CriticalPairs (FOTerm, subst, substList)
Trusted boundary: none (fully proved)
Main exports: substComp, subst_comp, single, occurs, unify, unify_sound
Open obligations: completeness (unifiable terms unify), most-generality (any unifier factors through the
  result), and the resulting effective critical-pair check are not yet proved here.
-/
import MeTTaILProofs.CriticalPairs

namespace MeTTaIL.CP

/-- Composition of substitutions: apply `ρ` then `σ`. -/
def substComp (σ ρ : Nat → FOTerm) : Nat → FOTerm := fun n => subst σ (ρ n)

mutual
  /-- Substitution composition: applying `ρ` then `σ` is applying the composite. -/
  theorem subst_comp (σ ρ : Nat → FOTerm) :
      ∀ t : FOTerm, subst σ (subst ρ t) = subst (substComp σ ρ) t
    | .var x => rfl
    | .app f args => by simp only [subst]; rw [substList_comp σ ρ args]
  theorem substList_comp (σ ρ : Nat → FOTerm) :
      ∀ args : List FOTerm, substList σ (substList ρ args) = substList (substComp σ ρ) args
    | [] => rfl
    | a :: as => by simp only [substList]; rw [subst_comp σ ρ a, substList_comp σ ρ as]
end

/-- The substitution sending `x` to `u` and every other variable to itself. -/
def single (x : Nat) (u : FOTerm) : Nat → FOTerm := Function.update FOTerm.var x u

@[simp] theorem single_same (x : Nat) (u : FOTerm) : single x u x = u := by
  simp [single]

mutual
  /-- Whether a variable occurs in a term (the occurs check). -/
  def occurs (x : Nat) : FOTerm → Bool
    | .var y => x == y
    | .app _ args => occursList x args
  def occursList (x : Nat) : List FOTerm → Bool
    | [] => false
    | a :: as => occurs x a || occursList x as
end

mutual
  /-- A variable that does not occur in a term is left untouched by binding it. -/
  theorem subst_single_of_not_occurs {x : Nat} {u : FOTerm} :
      ∀ {z : FOTerm}, occurs x z = false → subst (single x u) z = z
    | .var y, h => by
        simp only [occurs, beq_eq_false_iff_ne, ne_eq] at h
        simp only [subst, single, Function.update_apply, if_neg (fun he : y = x => h he.symm)]
    | .app f args, h => by
        simp only [occurs] at h
        simp only [subst]; rw [substList_single_of_not_occurs h]
  theorem substList_single_of_not_occurs {x : Nat} {u : FOTerm} :
      ∀ {zs : List FOTerm}, occursList x zs = false → substList (single x u) zs = zs
    | [], _ => rfl
    | a :: as, h => by
        simp only [occursList, Bool.or_eq_false_iff] at h
        simp only [substList]
        rw [subst_single_of_not_occurs h.1, substList_single_of_not_occurs h.2]
end

/-- Apply a substitution to both sides of an equation. -/
def substEq (ρ : Nat → FOTerm) (e : FOTerm × FOTerm) : FOTerm × FOTerm := (subst ρ e.1, subst ρ e.2)

/-- First-order syntactic unification of a list of equations. Bindings are applied eagerly to the remaining
    equations and composed into the result. `fuel` bounds the recursion; it succeeds with enough fuel on any
    unifiable input (completeness, proved separately). -/
def unify : Nat → List (FOTerm × FOTerm) → Option (Nat → FOTerm)
  | 0, _ => none
  | _ + 1, [] => some FOTerm.var
  | f + 1, (s, t) :: rest =>
      match s, t with
      | .var x, .var y =>
          if x = y then unify f rest
          else (unify f (rest.map (substEq (single x (.var y))))).map (substComp · (single x (.var y)))
      | .var x, .app gs bs =>
          if occurs x (.app gs bs) then none
          else (unify f (rest.map (substEq (single x (.app gs bs))))).map (substComp · (single x (.app gs bs)))
      | .app fs as, .var y =>
          if occurs y (.app fs as) then none
          else (unify f (rest.map (substEq (single y (.app fs as))))).map (substComp · (single y (.app fs as)))
      | .app fs as, .app gs bs =>
          if fs = gs ∧ as.length = bs.length then unify f (as.zip bs ++ rest) else none

/-- A substitution unifies a list of equations when it equates both sides of each. -/
def Unifies (σ : Nat → FOTerm) (eqs : List (FOTerm × FOTerm)) : Prop :=
  ∀ e ∈ eqs, subst σ e.1 = subst σ e.2

/-- Binding a non-occurring variable leaves a different variable alone. -/
theorem single_ne {x y : Nat} (u : FOTerm) (h : x ≠ y) : single x u y = .var y := by
  simp [single, Function.update_apply, if_neg (fun he : y = x => h he.symm)]

/-- A substitution composed via `substComp` distributes over `subst`. -/
theorem subst_substComp (σ' ρ : Nat → FOTerm) (z : FOTerm) :
    subst (substComp σ' ρ) z = subst σ' (subst ρ z) := (subst_comp σ' ρ z).symm

/-- If a substitution unifies every pair of two equal-length lists, it equalises the lists. -/
theorem substList_of_zip_unifies {σ : Nat → FOTerm} :
    ∀ {as bs : List FOTerm}, as.length = bs.length →
      (∀ e ∈ as.zip bs, subst σ e.1 = subst σ e.2) → substList σ as = substList σ bs
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hlen, h => by
      simp only [substList]
      have hhead : subst σ a = subst σ b := h (a, b) (by simp [List.zip])
      have htail : substList σ as = substList σ bs :=
        substList_of_zip_unifies (by simpa using hlen)
          (fun e he => h e (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr he))
      rw [hhead, htail]

/-- Soundness of unification: a returned substitution unifies every input equation. -/
theorem unify_sound : ∀ (f : Nat) (eqs : List (FOTerm × FOTerm)) (σ : Nat → FOTerm),
    unify f eqs = some σ → Unifies σ eqs
  | 0, _, _, h => by simp [unify] at h
  | _ + 1, [], σ, h => by
      simp only [unify, Option.some.injEq] at h; subst h; intro e he; simp at he
  | f + 1, (s, t) :: rest, σ, h => by
      have key : ∀ (x : Nat) (u : FOTerm), occurs x u = false →
          (unify f (rest.map (substEq (single x u)))).map (substComp · (single x u)) = some σ →
          subst σ (.var x) = subst σ u ∧ Unifies σ rest := by
        intro x u hocc hmap
        simp only [Option.map_eq_some_iff] at hmap
        obtain ⟨σ', hσ', rfl⟩ := hmap
        have ih := unify_sound f _ σ' hσ'
        refine ⟨?_, ?_⟩
        · have h1 : subst (substComp σ' (single x u)) (.var x) = subst σ' u := by
            rw [subst_substComp]; simp [subst, single_same]
          have h2 : subst (substComp σ' (single x u)) u = subst σ' u := by
            rw [subst_substComp, subst_single_of_not_occurs hocc]
          rw [h1, h2]
        · intro e he
          have := ih (substEq (single x u) e) (by
            simp only [List.mem_map]; exact ⟨e, he, rfl⟩)
          simpa only [substEq, subst_substComp] using this
      intro e he
      simp only [List.mem_cons] at he
      cases s with
      | var x =>
          cases t with
          | var y =>
              simp only [unify] at h
              split at h
              · rename_i hxy; subst hxy
                have ih := unify_sound f rest σ h
                rcases he with rfl | he
                · rfl
                · exact ih e he
              · rename_i hxy
                obtain ⟨heq, hrest⟩ :=
                  key x (.var y) (by simp only [occurs, beq_eq_false_iff_ne]; exact hxy) h
                rcases he with rfl | he
                · exact heq
                · exact hrest e he
          | app gs bs =>
              simp only [unify] at h
              split at h
              · simp at h
              · rename_i hocc
                obtain ⟨heq, hrest⟩ := key x (.app gs bs) (Bool.not_eq_true _ ▸ hocc) h
                rcases he with rfl | he
                · exact heq
                · exact hrest e he
      | app fs as =>
          cases t with
          | var y =>
              simp only [unify] at h
              split at h
              · simp at h
              · rename_i hocc
                obtain ⟨heq, hrest⟩ := key y (.app fs as) (Bool.not_eq_true _ ▸ hocc) h
                rcases he with rfl | he
                · exact heq.symm
                · exact hrest e he
          | app gs bs =>
              simp only [unify] at h
              split at h
              · rename_i hc
                have ih := unify_sound f _ σ h
                rcases he with rfl | he
                · show subst σ (.app fs as) = subst σ (.app gs bs)
                  simp only [subst, hc.1]
                  rw [substList_of_zip_unifies hc.2 (fun e' he' => ih e' (by simp [he']))]
                · exact ih e (by simp [he])
              · simp at h

mutual
  /-- `subst` depends only on the substitution's values, pointwise. -/
  theorem subst_funext {σ1 σ2 : Nat → FOTerm} (h : ∀ n, σ1 n = σ2 n) :
      ∀ z : FOTerm, subst σ1 z = subst σ2 z
    | .var x => h x
    | .app _ args => by simp only [subst]; rw [substList_funext h args]
  theorem substList_funext {σ1 σ2 : Nat → FOTerm} (h : ∀ n, σ1 n = σ2 n) :
      ∀ zs : List FOTerm, substList σ1 zs = substList σ2 zs
    | [] => rfl
    | a :: as => by simp only [substList]; rw [subst_funext h a, substList_funext h as]
end

/-- Composing a unifier `θ` of `x` and `u` with the binding `[x := u]` gives back `θ`. -/
theorem substComp_single_eq {θ : Nat → FOTerm} {x : Nat} {u : FOTerm} (h : subst θ (.var x) = subst θ u) :
    ∀ n, substComp θ (single x u) n = θ n := by
  intro n
  by_cases hn : n = x
  · subst hn; simp only [substComp, single_same]; exact h.symm
  · simp only [substComp, single_ne u (fun he : x = n => hn he.symm), subst]

/-- If a substitution equalises two lists, it unifies their zipped pairs. -/
theorem zip_unifies_of_substList {θ : Nat → FOTerm} :
    ∀ {as bs : List FOTerm}, substList θ as = substList θ bs →
      ∀ e ∈ as.zip bs, subst θ e.1 = subst θ e.2
  | [], _, _, _, he => by simp [List.zip] at he
  | _ :: _, [], _, _, he => by simp [List.zip] at he
  | a :: as, b :: bs, h, e, he => by
      simp only [substList, List.cons.injEq] at h
      simp only [List.zip_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact h.1
      · exact zip_unifies_of_substList h.2 e he

/-- A unifier survives applying one of its own bindings to the remaining equations. -/
theorem unifies_map_substEq {θ : Nat → FOTerm} {rest : List (FOTerm × FOTerm)}
    (hθrest : Unifies θ rest) {x : Nat} {u : FOTerm} (hxu : subst θ (.var x) = subst θ u) :
    Unifies θ (rest.map (substEq (single x u))) := by
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨e0, he0, rfl⟩ := he
  show subst θ (subst (single x u) e0.1) = subst θ (subst (single x u) e0.2)
  rw [subst_comp, subst_comp, subst_funext (substComp_single_eq hxu) e0.1,
    subst_funext (substComp_single_eq hxu) e0.2]
  exact hθrest e0 he0

/-- Most-generality: every unifier of the input equations factors through the substitution unification
    returns, so that substitution is a most general unifier. -/
theorem unify_mgu : ∀ (f : Nat) (eqs : List (FOTerm × FOTerm)) (σ θ : Nat → FOTerm),
    unify f eqs = some σ → Unifies θ eqs → ∃ ρ, ∀ n, θ n = subst ρ (σ n)
  | 0, _, _, _, h, _ => by simp [unify] at h
  | _ + 1, [], σ, θ, h, _ => by
      simp only [unify, Option.some.injEq] at h; subst h; exact ⟨θ, fun _ => rfl⟩
  | f + 1, (s, t) :: rest, σ, θ, h, hθ => by
      have hθst : subst θ s = subst θ t := hθ (s, t) (by simp)
      have hθrest : Unifies θ rest := fun e he => hθ e (by simp [he])
      have key : ∀ (x : Nat) (u : FOTerm), subst θ (.var x) = subst θ u →
          (unify f (rest.map (substEq (single x u)))).map (substComp · (single x u)) = some σ →
          ∃ ρ, ∀ n, θ n = subst ρ (σ n) := by
        intro x u hxu hmap
        simp only [Option.map_eq_some_iff] at hmap
        obtain ⟨σ', hσ', rfl⟩ := hmap
        have hθsub : Unifies θ (rest.map (substEq (single x u))) := unifies_map_substEq hθrest hxu
        obtain ⟨ρ, hρ⟩ := unify_mgu f _ σ' θ hσ' hθsub
        refine ⟨ρ, fun n => ?_⟩
        calc θ n = subst θ (single x u n) := (substComp_single_eq hxu n).symm
          _ = subst (substComp ρ σ') (single x u n) := subst_funext hρ _
          _ = subst ρ (subst σ' (single x u n)) := (subst_comp ρ σ' _).symm
          _ = subst ρ (substComp σ' (single x u) n) := rfl
      cases s with
      | var x =>
          cases t with
          | var y =>
              simp only [unify] at h
              split at h
              · rename_i hxy; subst hxy; exact unify_mgu f rest σ θ h hθrest
              · exact key x (.var y) hθst h
          | app gs bs =>
              simp only [unify] at h
              split at h
              · simp at h
              · exact key x (.app gs bs) hθst h
      | app fs as =>
          cases t with
          | var y =>
              simp only [unify] at h
              split at h
              · simp at h
              · exact key y (.app fs as) hθst.symm h
          | app gs bs =>
              simp only [unify] at h
              split at h
              · rename_i hc
                refine unify_mgu f _ σ θ h ?_
                intro e he
                simp only [List.mem_append] at he
                rcases he with he | he
                · have hsub : substList θ as = substList θ bs := by
                    have hst := hθst; simp only [subst, FOTerm.app.injEq] at hst; exact hst.2
                  exact zip_unifies_of_substList hsub e he
                · exact hθrest e he
              · simp at h

/-! ### Toward completeness: the occurs check never rejects a unifiable pair -/

mutual
  /-- Term size. -/
  def size : FOTerm → Nat
    | .var _ => 1
    | .app _ args => 1 + sizeList args
  def sizeList : List FOTerm → Nat
    | [] => 0
    | a :: as => size a + sizeList as
end

mutual
  /-- If `x` occurs in `u`, the image of `x` is no larger than the image of `u`. -/
  theorem occurs_size_le {θ : Nat → FOTerm} {x : Nat} :
      ∀ {u : FOTerm}, occurs x u = true → size (θ x) ≤ size (subst θ u)
    | .var y, h => by simp only [occurs, beq_iff_eq] at h; subst h; simp [subst]
    | .app _ args, h => by
        simp only [occurs] at h
        simp only [subst, size]
        have := occursList_size_le (θ := θ) h
        omega
  theorem occursList_size_le {θ : Nat → FOTerm} {x : Nat} :
      ∀ {args : List FOTerm}, occursList x args = true → size (θ x) ≤ sizeList (substList θ args)
    | [], h => by simp [occursList] at h
    | a :: as, h => by
        simp only [occursList, Bool.or_eq_true] at h
        simp only [substList, sizeList]
        rcases h with h | h
        · have := occurs_size_le (θ := θ) h; omega
        · have := occursList_size_le (θ := θ) h; omega
end

/-- Occurs-check soundness: if `θ` unifies `x` with `u` and `x` occurs in `u`, then `u` is just `x`. So a
    failing occurs check (a proper occurrence) means the pair is not unifiable. -/
theorem occurs_check_sound {θ : Nat → FOTerm} {x : Nat} :
    ∀ {u : FOTerm}, subst θ (.var x) = subst θ u → occurs x u = true → u = .var x
  | .var y, _, h => by simp only [occurs, beq_iff_eq] at h; subst h; rfl
  | .app f args, heq, h => by
      exfalso
      simp only [occurs] at h
      have hle := occursList_size_le (θ := θ) h
      have hsize : size (subst θ (.var x)) = size (subst θ (.app f args)) := by rw [heq]
      simp only [subst, size] at hsize
      omega

mutual
  /-- The set of variables of a term. -/
  def varsFin : FOTerm → Finset Nat
    | .var n => {n}
    | .app _ args => varsFinList args
  def varsFinList : List FOTerm → Finset Nat
    | [] => ∅
    | a :: as => varsFin a ∪ varsFinList as
end

mutual
  /-- Membership in the variable set is the occurs check. -/
  theorem mem_varsFin_iff_occurs {x : Nat} : ∀ {t : FOTerm}, x ∈ varsFin t ↔ occurs x t = true
    | .var y => by simp only [varsFin, occurs, Finset.mem_singleton, beq_iff_eq]
    | .app _ args => by simp only [varsFin, occurs]; exact mem_varsFinList_iff_occursList
  theorem mem_varsFinList_iff_occursList {x : Nat} :
      ∀ {args : List FOTerm}, x ∈ varsFinList args ↔ occursList x args = true
    | [] => by simp [varsFinList, occursList]
    | a :: as => by
        simp only [varsFinList, occursList, Finset.mem_union, Bool.or_eq_true]
        rw [mem_varsFin_iff_occurs, mem_varsFinList_iff_occursList]
end

mutual
  /-- Substituting `[x := u]` replaces `x`'s occurrences by `u`'s variables and removes `x`. -/
  theorem vars_subst_single_subset {x : Nat} {u : FOTerm} :
      ∀ {t : FOTerm}, varsFin (subst (single x u) t) ⊆ (varsFin t \ {x}) ∪ varsFin u
    | .var y => by
        intro z hz
        by_cases hy : y = x
        · subst hy; rw [subst, single_same] at hz
          simp only [Finset.mem_union]; right; exact hz
        · rw [subst, single_ne u (fun he : x = y => hy he.symm)] at hz
          simp only [varsFin, Finset.mem_singleton] at hz; subst hz
          simp only [Finset.mem_union, Finset.mem_sdiff, varsFin, Finset.mem_singleton]
          tauto
    | .app _ args => by simp only [subst, varsFin]; exact vars_subst_single_subset_list
  theorem vars_subst_single_subset_list {x : Nat} {u : FOTerm} :
      ∀ {args : List FOTerm}, varsFinList (substList (single x u) args) ⊆ (varsFinList args \ {x}) ∪ varsFin u
    | [] => by simp [substList, varsFinList]
    | a :: as => by
        simp only [substList, varsFinList]
        intro z hz
        simp only [Finset.mem_union] at hz
        rcases hz with hz | hz
        · have := vars_subst_single_subset (t := a) hz
          simp only [Finset.mem_union, Finset.mem_sdiff] at this ⊢
          tauto
        · have := vars_subst_single_subset_list (args := as) hz
          simp only [Finset.mem_union, Finset.mem_sdiff] at this ⊢
          tauto
end

/-- The variable set of an equation. -/
def varsEq (e : FOTerm × FOTerm) : Finset Nat := varsFin e.1 ∪ varsFin e.2

/-- The variable set of an equation list. -/
def varsEqs : List (FOTerm × FOTerm) → Finset Nat
  | [] => ∅
  | e :: es => varsEq e ∪ varsEqs es

/-- The number of distinct variables in an equation list (first measure component). -/
def numVars (eqs : List (FOTerm × FOTerm)) : Nat := (varsEqs eqs).card

/-- The total size of an equation. -/
def sizeEq (e : FOTerm × FOTerm) : Nat := size e.1 + size e.2

/-- The total size of an equation list (second measure component). -/
def sizeEqs : List (FOTerm × FOTerm) → Nat
  | [] => 0
  | e :: es => sizeEq e + sizeEqs es

theorem sizeEqs_append : ∀ l1 l2 : List (FOTerm × FOTerm), sizeEqs (l1 ++ l2) = sizeEqs l1 + sizeEqs l2
  | [], _ => by simp [sizeEqs]
  | e :: es, l2 => by simp only [List.cons_append, sizeEqs]; rw [sizeEqs_append es l2]; omega

theorem varsEqs_append :
    ∀ l1 l2 : List (FOTerm × FOTerm), varsEqs (l1 ++ l2) = varsEqs l1 ∪ varsEqs l2
  | [], _ => by simp [varsEqs]
  | e :: es, l2 => by
      simp only [List.cons_append, varsEqs]; rw [varsEqs_append es l2, Finset.union_assoc]

theorem sizeEqs_zip : ∀ {as bs : List FOTerm}, as.length = bs.length →
    sizeEqs (as.zip bs) = sizeList as + sizeList bs
  | [], [], _ => by simp [List.zip, sizeEqs, sizeList]
  | a :: as, b :: bs, hlen => by
      simp only [List.zip_cons_cons, sizeEqs, sizeEq, sizeList]
      rw [sizeEqs_zip (by simpa using hlen)]; omega

theorem varsEqs_zip : ∀ {as bs : List FOTerm}, as.length = bs.length →
    varsEqs (as.zip bs) = varsFinList as ∪ varsFinList bs
  | [], [], _ => by simp [List.zip, varsEqs, varsFinList]
  | a :: as, b :: bs, hlen => by
      simp only [List.zip_cons_cons, varsEqs, varsEq, varsFinList]
      rw [varsEqs_zip (by simpa using hlen)]
      ext z; simp only [Finset.mem_union]; tauto

/-- Applying `[x := u]` to an equation list keeps its variables within those of the original (minus `x`)
    plus `u`'s. -/
theorem varsEqs_map_substEq_subset {x : Nat} {u : FOTerm} :
    ∀ {rest : List (FOTerm × FOTerm)},
      varsEqs (rest.map (substEq (single x u))) ⊆ (varsEqs rest \ {x}) ∪ varsFin u
  | [] => by simp [varsEqs]
  | e :: es => by
      simp only [List.map_cons, varsEqs, varsEq, substEq]
      intro z hz
      simp only [Finset.mem_union] at hz
      rcases hz with (hz | hz) | hz
      · have hh := vars_subst_single_subset hz
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hh ⊢
        tauto
      · have hh := vars_subst_single_subset hz
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hh ⊢
        tauto
      · have hh := varsEqs_map_substEq_subset hz
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hh ⊢
        tauto

/-- A variable-elimination step strictly drops the distinct-variable count. -/
theorem numVars_var_elim_lt {x : Nat} {u : FOTerm} {rest : List (FOTerm × FOTerm)}
    (hu : x ∉ varsFin u) :
    numVars (rest.map (substEq (single x u))) < numVars ((.var x, u) :: rest) := by
  have hx : x ∈ varsEqs ((.var x, u) :: rest) := by
    simp [varsEqs, varsEq, varsFin]
  have hsub : varsEqs (rest.map (substEq (single x u))) ⊆ varsEqs ((.var x, u) :: rest) \ {x} := by
    intro z hz
    have := varsEqs_map_substEq_subset (x := x) (u := u) (rest := rest) hz
    simp only [Finset.mem_sdiff, Finset.mem_singleton, varsEqs, varsEq, varsFin,
      Finset.mem_union, Finset.mem_sdiff] at this ⊢
    rcases this with ⟨hzr, hzx⟩ | hzu
    · exact ⟨Or.inr hzr, hzx⟩
    · exact ⟨Or.inl (Or.inr hzu), fun he => hu (he ▸ hzu)⟩
  calc numVars (rest.map (substEq (single x u)))
      ≤ (varsEqs ((.var x, u) :: rest) \ {x}).card := Finset.card_le_card hsub
    _ < (varsEqs ((.var x, u) :: rest)).card :=
        Finset.card_lt_card (Finset.sdiff_ssubset (Finset.singleton_subset_iff.mpr hx)
          (Finset.singleton_nonempty x))

/-- A decompose step keeps the distinct-variable count unchanged. -/
theorem numVars_decompose_eq {fs gs : String} {as bs : List FOTerm} {rest : List (FOTerm × FOTerm)}
    (hlen : as.length = bs.length) :
    numVars (as.zip bs ++ rest) = numVars ((.app fs as, .app gs bs) :: rest) := by
  unfold numVars
  congr 1
  rw [varsEqs_append, varsEqs_zip hlen]
  simp only [varsEqs, varsEq, varsFin, Finset.union_assoc]

/-- The distinct-variable count is symmetric in an equation's two sides. -/
theorem numVars_cons_comm {a b : FOTerm} {rest : List (FOTerm × FOTerm)} :
    numVars ((a, b) :: rest) = numVars ((b, a) :: rest) := by
  unfold numVars; congr 1
  simp only [varsEqs, varsEq]; rw [Finset.union_comm (varsFin a) (varsFin b)]

/-- Substitution preserves list length. -/
theorem substList_length (θ : Nat → FOTerm) : ∀ l : List FOTerm, (substList θ l).length = l.length
  | [] => rfl
  | a :: as => by simp only [substList, List.length_cons]; rw [substList_length θ as]

/-- Lexicographic step for the termination measure. -/
theorem measure_lt {a b c d : Nat} (h : a < c ∨ a = c ∧ b < d) :
    Prod.Lex (· < ·) (· < ·) (a, b) (c, d) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

/-- Completeness: a unifiable list of equations is unified by `unify` with enough fuel. The recursion is on
    the lexicographic (distinct-variable-count, total-size) measure: variable elimination drops the variable
    count, and decompose keeps it while dropping the size. The occurs check never rejects (occurs_check_sound),
    since the input is unifiable. The pattern match is at the equation level so the termination measure sees
    each concrete head shape. -/
theorem unify_complete : ∀ (eqs : List (FOTerm × FOTerm)) (θ : Nat → FOTerm),
    Unifies θ eqs → ∃ f σ, unify f eqs = some σ
  | [], _, _ => ⟨1, FOTerm.var, rfl⟩
  | (.var x, .var y) :: rest, θ, hθ => by
      have hθst : subst θ (.var x) = subst θ (.var y) := hθ (.var x, .var y) (by simp)
      have hθrest : Unifies θ rest := fun e he => hθ e (by simp [he])
      by_cases hxy : x = y
      · obtain ⟨f, σ, hf⟩ := unify_complete rest θ hθrest
        exact ⟨f + 1, σ, by simp only [unify]; rw [if_pos hxy]; exact hf⟩
      · obtain ⟨f, σ, hf⟩ := unify_complete _ θ (unifies_map_substEq hθrest hθst)
        exact ⟨f + 1, substComp σ (single x (.var y)), by simp only [unify]; rw [if_neg hxy, hf]; rfl⟩
  | (.var x, .app gs bs) :: rest, θ, hθ => by
      have hθst : subst θ (.var x) = subst θ (.app gs bs) := hθ (.var x, .app gs bs) (by simp)
      have hθrest : Unifies θ rest := fun e he => hθ e (by simp [he])
      have hocc : occurs x (.app gs bs) = false := by
        cases hh : occurs x (.app gs bs) with
        | false => rfl
        | true => exact absurd (occurs_check_sound hθst hh) (by simp)
      obtain ⟨f, σ, hf⟩ := unify_complete _ θ (unifies_map_substEq hθrest hθst)
      exact ⟨f + 1, substComp σ (single x (.app gs bs)), by
        simp only [unify]; rw [if_neg (by simp [hocc]), hf]; rfl⟩
  | (.app fs as, .var y) :: rest, θ, hθ => by
      have hθst : subst θ (.app fs as) = subst θ (.var y) := hθ (.app fs as, .var y) (by simp)
      have hθrest : Unifies θ rest := fun e he => hθ e (by simp [he])
      have hocc : occurs y (.app fs as) = false := by
        cases hh : occurs y (.app fs as) with
        | false => rfl
        | true => exact absurd (occurs_check_sound hθst.symm hh) (by simp)
      obtain ⟨f, σ, hf⟩ := unify_complete _ θ (unifies_map_substEq hθrest hθst.symm)
      exact ⟨f + 1, substComp σ (single y (.app fs as)), by
        simp only [unify]; rw [if_neg (by simp [hocc]), hf]; rfl⟩
  | (.app fs as, .app gs bs) :: rest, θ, hθ => by
      have hθst : subst θ (.app fs as) = subst θ (.app gs bs) := hθ (.app fs as, .app gs bs) (by simp)
      have hθrest : Unifies θ rest := fun e he => hθ e (by simp [he])
      simp only [subst, FOTerm.app.injEq] at hθst
      have hfg : fs = gs ∧ as.length = bs.length := by
        refine ⟨hθst.1, ?_⟩
        have := congrArg List.length hθst.2
        rwa [substList_length, substList_length] at this
      have hθsub : Unifies θ (as.zip bs ++ rest) := by
        intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · exact zip_unifies_of_substList hθst.2 e he
        · exact hθrest e he
      obtain ⟨f, σ, hf⟩ := unify_complete _ θ hθsub
      exact ⟨f + 1, σ, by simp only [unify]; rw [if_pos hfg]; exact hf⟩
  termination_by eqs => (numVars eqs, sizeEqs eqs)
  decreasing_by
    · exact measure_lt (by
        by_cases hc : numVars rest = numVars ((.var x, .var y) :: rest)
        · exact Or.inr ⟨hc, by simp only [sizeEqs, sizeEq, size]; omega⟩
        · exact Or.inl (lt_of_le_of_ne
            (Finset.card_le_card (by simp only [varsEqs]; exact Finset.subset_union_right)) hc))
    · exact measure_lt (Or.inl (numVars_var_elim_lt (by
        simp only [varsFin, Finset.mem_singleton]; exact hxy)))
    · exact measure_lt (Or.inl (numVars_var_elim_lt (by rw [mem_varsFin_iff_occurs, hocc]; simp)))
    · exact measure_lt (by
        rw [numVars_cons_comm]
        exact Or.inl (numVars_var_elim_lt (by rw [mem_varsFin_iff_occurs, hocc]; simp)))
    · exact measure_lt (Or.inr ⟨numVars_decompose_eq hfg.2, by
        rw [sizeEqs_append, sizeEqs_zip hfg.2]; simp only [sizeEqs, sizeEq, size]; omega⟩)

end MeTTaIL.CP
