import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: substitution and instantiation

Foundational lemmas about `Subst.apply` (capture-free first-order substitution over `Atom`) and
`instantiate` (`Subst.apply` of `bindingsToSubst`), reused throughout the metatheory layer.

Substitution does **not** preserve `Atom.size`: a variable (size `1`) may be replaced by a
larger atom, so the invariant is *monotonicity*: `a.size ≤ (Subst.apply s a).size`. On
variable-free atoms substitution is the identity, and the empty substitution is the identity
everywhere.
-/

namespace Metta

/-- Every atom has size at least one. -/
theorem Atom.one_le_size (a : Atom) : 1 ≤ a.size := by
  cases a <;> simp only [Atom.size] <;> omega

/-- The empty substitution is the identity. -/
theorem Subst.apply_nil (a : Atom) : Subst.apply [] a = a := by
  induction a with
  | var x => simp [Subst.apply, Subst.lookup]
  | expr xs ih => simp only [Subst.apply]; rw [List.map_congr_left ih]; simp
  | _ => simp [Subst.apply]

/-- Instantiating under the empty binding set is the identity. -/
theorem instantiate_nil (a : Atom) : instantiate [] a = a := by
  simp only [instantiate, bindingsToSubst, List.foldr_nil]
  exact Subst.apply_nil a

/-- A variable-free atom is fixed by every substitution. -/
theorem Subst.apply_of_closed (s : Subst) : ∀ a : Atom, a.vars = [] → Subst.apply s a = a := by
  intro a
  induction a with
  | var x => intro h; simp [Atom.vars] at h
  | expr xs ih =>
      intro h
      simp only [Atom.vars] at h
      rw [List.flatten_eq_nil_iff] at h
      simp only [Subst.apply]
      have hx : ∀ x ∈ xs, Subst.apply s x = x := fun x hxmem =>
        ih x hxmem (h (Atom.vars x) (List.mem_map_of_mem hxmem))
      rw [List.map_congr_left hx]; simp
  | _ => intro _; simp [Subst.apply]

/-- A variable-free atom is fixed by every `instantiate`. -/
theorem instantiate_of_closed (b : Bindings) (a : Atom) (h : a.vars = []) :
    instantiate b a = a :=
  Subst.apply_of_closed _ a h

/-- Substitution can only grow an atom: `Atom.size` is monotone under `Subst.apply` (a variable
may be replaced by a strictly larger atom, never a smaller one). -/
theorem Subst.apply_size_le (s : Subst) (a : Atom) : a.size ≤ (Subst.apply s a).size := by
  induction a with
  | var x => simp only [Subst.apply, Atom.size]; exact Atom.one_le_size _
  | expr xs ih =>
      simp only [Subst.apply, Atom.size]
      have hsum : (xs.map Atom.size).sum ≤ ((xs.map (Subst.apply s)).map Atom.size).sum := by
        rw [List.map_map]
        exact List.sum_le_sum (fun x hx => ih x hx)
      omega
  | _ => simp [Subst.apply, Atom.size]

/-- `Atom.size` is monotone under `instantiate`. -/
theorem instantiate_size_le (b : Bindings) (a : Atom) : a.size ≤ (instantiate b a).size :=
  Subst.apply_size_le _ a

/-- Lookup in a concatenated substitution consults the left one first. -/
theorem Subst.lookup_append (s₁ s₂ : Subst) (x : VarName) :
    Subst.lookup (s₁ ++ s₂) x = (Subst.lookup s₁ x).orElse (fun _ => Subst.lookup s₂ x) := by
  induction s₁ with
  | nil => simp [Subst.lookup]
  | cons p s₁ ih =>
      obtain ⟨y, a⟩ := p
      simp only [List.cons_append, Subst.lookup]
      by_cases h : (x == y) = true
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]; exact ih

/-- Mapping a function over the values of a substitution maps it through `lookup`. -/
theorem Subst.lookup_map_snd (f : Atom → Atom) (s : Subst) (x : VarName) :
    Subst.lookup (s.map (fun p => (p.1, f p.2))) x = (Subst.lookup s x).map f := by
  induction s with
  | nil => simp [Subst.lookup]
  | cons p s ih =>
      obtain ⟨y, a⟩ := p
      simp only [List.map_cons, Subst.lookup]
      by_cases h : (x == y) = true
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]; exact ih

/-- **Substitution composition law.** `compose s₁ s₂` denotes "apply `s₂`, then `s₁`":
`Subst.apply (compose s₁ s₂)` is the composite `Subst.apply s₁ ∘ Subst.apply s₂`. The proof
recurses on `a`; the variable case reduces to `lookup_append` and `lookup_map_snd`. -/
theorem Subst.apply_compose (s₁ s₂ : Subst) (a : Atom) :
    Subst.apply (Subst.compose s₁ s₂) a = Subst.apply s₁ (Subst.apply s₂ a) := by
  induction a with
  | var x =>
      simp only [Subst.apply, Subst.compose]
      rw [Subst.lookup_append, Subst.lookup_map_snd]
      cases hl : Subst.lookup s₂ x <;> simp [Subst.apply]
  | expr xs ih =>
      simp only [Subst.apply, List.map_map]
      congr 1
      exact List.map_congr_left ih
  | _ => simp [Subst.apply, Subst.compose]

end Metta
