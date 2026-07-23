-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Substitution
Layer: Proofs
Purpose: Foundational lemmas about Subst.apply (capture-free first-order substitution over Atom) and
  equality-class-aware instantiate, reused across the metatheory layer. Covers empty-substitution
  identity, that closed atoms are fixed, size monotonicity (a variable may be replaced by a larger
  atom, so size only grows), and the substitution composition law Subst.apply_compose.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: Subst.apply_nil, instantiate_nil, Subst.apply_of_closed, instantiate_of_closed,
  Subst.apply_size_le, instantiate_size_le, Subst.lookup_append, Subst.lookup_map_snd,
  Subst.apply_compose
Open obligations: none
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: substitution and instantiation

Foundational lemmas about `Subst.apply` (capture-free first-order substitution over `Atom`) and
`instantiate` (recursive resolution through binding equality classes), reused throughout the
metatheory layer.

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
  induction a with
  | var x =>
      simp [instantiate, Bindings.resolveAtom, Bindings.resolve,
        Bindings.eqClassOrdered, Bindings.eqVarsInOrder]
  | expr xs ih =>
      simp only [instantiate, Bindings.resolveAtom]
      congr 1
      have hmap : List.map (Bindings.resolveAtom []) xs = List.map id xs :=
        List.map_congr_left (fun child hchild => by
          simpa [instantiate] using ih child hchild)
      simpa using hmap
  | _ => simp [instantiate, Bindings.resolveAtom]

/-- A singleton value binding does not resolve any different variable. -/
theorem Bindings.resolve_singleton_val_ne {key x : VarName} {value : Atom}
    (h : x ≠ key) :
    Bindings.resolve [BindingRel.val key value] x = none := by
  simp [Bindings.resolve, Bindings.eqClassOrdered,
    Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep,
    Bindings.eqVarsInOrder,
    Bindings.classValues_singleton_val_ne value h]

private theorem List.mapM_some_self_of_forall {α : Type} (f : α → Option α) :
    ∀ xs : List α, (∀ x ∈ xs, f x = some x) → xs.mapM f = some xs
  | [], _ => by simp
  | x :: xs, h => by
      simp [h x (by simp), List.mapM_some_self_of_forall f xs (fun y hy => h y (by simp [hy]))]

/-- Recursive binding resolution leaves a variable-free atom unchanged whenever
    the supplied fuel exceeds its structural size. -/
theorem Bindings.resolveAtomAux_of_closed (b : Bindings) :
    ∀ (a : Atom) (fuel : Nat) (visited : List VarName),
      a.vars = [] → a.size < fuel →
        Bindings.resolveAtomAux b fuel visited a = some a := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s fuel visited _ hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel => simp [Bindings.resolveAtomAux]
  · intro x fuel visited hclosed _
    simp [Atom.vars] at hclosed
  · intro g fuel visited _ hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel => simp [Bindings.resolveAtomAux]
  · intro xs ih fuel visited hclosed hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel =>
        have hmap : xs.mapM (Bindings.resolveAtomAux b fuel visited) = some xs := by
          apply List.mapM_some_self_of_forall
          intro child hchild
          have hchildClosed : child.vars = [] := by
            simp only [Atom.vars] at hclosed
            rw [List.flatten_eq_nil_iff] at hclosed
            exact hclosed child.vars (List.mem_map_of_mem hchild)
          have hchildLe : child.size ≤ (xs.map Atom.size).sum :=
            List.le_sum_of_mem (List.mem_map.mpr ⟨child, hchild, rfl⟩)
          have hchildSize : child.size < fuel := by
            simp only [Atom.size] at hsize
            omega
          exact ih child hchild fuel visited hchildClosed hchildSize
        simp [Bindings.resolveAtomAux, hmap]

/-- With the bound key marked as visited, a singleton binding leaves an atom
    that does not mention that key unchanged. -/
theorem Bindings.resolveAtomAux_singleton_val_inert (key : VarName) (value : Atom) :
    ∀ (a : Atom) (fuel : Nat), key ∉ a.vars → a.size < fuel →
      Bindings.resolveAtomAux [BindingRel.val key value] fuel [key] a = some a := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s fuel _ hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel => simp [Bindings.resolveAtomAux]
  · intro x fuel hnot hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel =>
        have hx : x ≠ key := by
          intro h
          apply hnot
          simpa [Atom.vars] using h.symm
        simp [Bindings.resolveAtomAux,
          Bindings.eqRepresentative, Bindings.eqClassOrdered, Bindings.eqClass,
          Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, hx]
  · intro g fuel _ hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel => simp [Bindings.resolveAtomAux]
  · intro xs ih fuel hnot hsize
    cases fuel with
    | zero => simp [Atom.size] at hsize
    | succ fuel =>
        have hmap : xs.mapM
            (Bindings.resolveAtomAux [BindingRel.val key value] fuel [key]) = some xs := by
          have hchildren : ∀ child ∈ xs,
              Bindings.resolveAtomAux [BindingRel.val key value] fuel [key] child =
                some child := by
            intro child hchild
            have hchildNot : key ∉ child.vars := by
              intro hv
              apply hnot
              simp only [Atom.vars, List.mem_flatten, List.mem_map]
              exact ⟨child.vars, ⟨child, hchild, rfl⟩, hv⟩
            have hchildLe : child.size ≤ (xs.map Atom.size).sum :=
              List.le_sum_of_mem (List.mem_map.mpr ⟨child, hchild, rfl⟩)
            have hchildSize : child.size < fuel := by
              simp only [Atom.size] at hsize
              omega
            exact ih child hchild fuel hchildNot hchildSize
          exact List.mapM_some_self_of_forall _ xs hchildren
        simp [Bindings.resolveAtomAux, hmap]

/-- Resolving the key of a fresh singleton binding returns its recursively
    resolved value, which is the value itself when it does not mention the key. -/
theorem Bindings.resolve_singleton_val_self_of_not_mem (key : VarName) (value : Atom)
    (hnot : key ∉ value.vars) :
    Bindings.resolve [BindingRel.val key value] key = some value := by
  cases value with
  | var x =>
      have hkx : key ≠ x := by simpa [Atom.vars] using hnot
      have hxk : x ≠ key := hkx.symm
      simp [Bindings.resolve,
        Bindings.resolveAtomAux, Bindings.resolutionFuel, Bindings.relationResolutionFuel,
        Bindings.eqRepresentative, Bindings.eqClassOrdered, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size,
        hxk]
  | sym s =>
      simp [Bindings.resolve,
        Bindings.resolveAtomAux, Bindings.resolutionFuel, Bindings.relationResolutionFuel,
        Bindings.eqClassOrdered, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size]
  | gnd g =>
      simp [Bindings.resolve,
        Bindings.resolveAtomAux, Bindings.resolutionFuel, Bindings.relationResolutionFuel,
        Bindings.eqClassOrdered, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size]
  | expr xs =>
      have hinert := Bindings.resolveAtomAux_singleton_val_inert key (Atom.expr xs)
        (Atom.expr xs) ((Atom.expr xs).size + 2) hnot (by omega)
      have hinert' : Bindings.resolveAtomAux
          [BindingRel.val key (Atom.expr xs)]
          (1 + (1 + (Atom.expr xs).size)) [key] (Atom.expr xs) =
          some (Atom.expr xs) := by
        have hfuel : (Atom.expr xs).size + 2 =
            1 + (1 + (Atom.expr xs).size) := by omega
        rw [← hfuel]
        exact hinert
      have haux : Bindings.resolveAtomAux
          [BindingRel.val key (Atom.expr xs)]
          (1 + Bindings.relationResolutionFuel
            (BindingRel.val key (Atom.expr xs))) [key] (Atom.expr xs) =
          some (Atom.expr xs) := by
        have hfuel : 1 + (1 + (Atom.expr xs).size) =
            1 + Bindings.relationResolutionFuel
              (BindingRel.val key (Atom.expr xs)) := by
          simp [Bindings.relationResolutionFuel]
          omega
        rw [← hfuel]
        exact hinert'
      simp [Bindings.resolve,
        Bindings.resolveAtomAux, Bindings.resolutionFuel,
        Bindings.eqClassOrdered, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size,
        haux]

/-- Instantiating a variable under a fresh singleton value binding returns that value. -/
theorem instantiate_singleton_val_var_of_not_mem (key : VarName) (value : Atom)
    (hnot : key ∉ value.vars) :
    instantiate [BindingRel.val key value] (Atom.var key) = value := by
  simp [instantiate, Bindings.resolveAtom,
    Bindings.resolve_singleton_val_self_of_not_mem key value hnot]

/-- At any positive fuel, a singleton value binding's resolver leaves every
    different variable untouched. -/
theorem Bindings.resolveAtomAux_singleton_val_unbound (key : VarName) (value : Atom)
    {x : VarName} (h : x ≠ key) (fuel : Nat) (hfuel : 0 < fuel) :
    Bindings.resolveAtomAux [BindingRel.val key value] fuel [] (Atom.var x) =
      some (Atom.var x) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp [Bindings.resolveAtomAux,
        Bindings.eqRepresentative, Bindings.eqClassOrdered, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder,
        Bindings.classValues_singleton_val_ne value h]

/-- The empty binding set has no dependency loop. -/
@[simp] theorem Bindings.hasLoop_empty :
    Bindings.hasLoop [] = false := by
  rfl

/-- A singleton value binding whose key is absent from its value has no direct
    or recursive dependency loop. -/
@[simp] theorem Bindings.hasLoop_singleton_val_of_not_mem (key : VarName) (value : Atom)
    (hnot : key ∉ value.vars) :
    Bindings.hasLoop [BindingRel.val key value] = false := by
  let direct : Bool := [BindingRel.val key value].any fun r =>
    match r with
    | BindingRel.val x (Atom.var y) => x == y
    | BindingRel.eq x y => x == y
    | _ => false
  have hdirect : direct = false := by
    cases value with
    | var x =>
        have hkx : key ≠ x := by simpa [Atom.vars] using hnot
        simp [direct, hkx]
    | sym _ => simp [direct]
    | gnd _ => simp [direct]
    | expr _ => simp [direct]
  have hkey : Bindings.resolveAtomAux [BindingRel.val key value]
      (Bindings.resolutionFuel [BindingRel.val key value] (Atom.var key)) []
      (Atom.var key) = some value := by
    have hresolve := Bindings.resolve_singleton_val_self_of_not_mem key value hnot
    simpa [Bindings.resolve, Bindings.eqClassOrdered, Bindings.eqVarsInOrder,
      Bindings.eqClass, Bindings.eqClassAux,
      Bindings.eqStep] using hresolve
  unfold Bindings.hasLoop
  change (direct ||
    (Bindings.vars [BindingRel.val key value]).any fun x =>
      (Bindings.resolveAtomAux [BindingRel.val key value]
        (Bindings.resolutionFuel [BindingRel.val key value] (Atom.var x)) []
        (Atom.var x)).isNone) = false
  rw [hdirect, Bool.false_or, List.any_eq_false]
  intro x _hx
  by_cases hx : x = key
  · subst x
    simp [hkey]
  · have hunbound := Bindings.resolveAtomAux_singleton_val_unbound key value hx
      (Bindings.resolutionFuel [BindingRel.val key value] (Atom.var x)) (by
        simp [Bindings.resolutionFuel])
    simp [hunbound]

/-- A non-reflexive singleton equality class cannot contain either a direct
    self-loop or a recursive value dependency. -/
@[simp] theorem Bindings.hasLoop_singleton_eq_of_ne (x y : VarName)
    (hne : x ≠ y) :
    Bindings.hasLoop [BindingRel.eq x y] = false := by
  simp [Bindings.hasLoop, Bindings.vars, List.eraseDups_cons,
    Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.eqRepresentative, Bindings.eqClassOrdered,
    Bindings.classValues, Bindings.lookupVal,
    Bindings.eqVarsInOrder, Bindings.eqClass, Bindings.eqClassAux,
    Bindings.eqStep, hne, Ne.symm hne]

/-- A singleton value binding is inert on atoms that do not mention its key. -/
theorem instantiate_singleton_val_inert (key : VarName) (value : Atom) :
    ∀ a : Atom, key ∉ a.vars → instantiate [BindingRel.val key value] a = a := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s _
    simp [instantiate, Bindings.resolveAtom]
  · intro x hnot
    have hx : x ≠ key := by
      intro h
      apply hnot
      simpa [Atom.vars] using h.symm
    simp [instantiate, Bindings.resolveAtom, Bindings.resolve_singleton_val_ne hx]
  · intro g _
    simp [instantiate, Bindings.resolveAtom]
  · intro xs ih hnot
    simp only [instantiate, Bindings.resolveAtom]
    congr 1
    have hmap : List.map (Bindings.resolveAtom [BindingRel.val key value]) xs =
        List.map id xs := List.map_congr_left (fun child hchild => by
      have hchildNot : key ∉ child.vars := by
        intro hv
        apply hnot
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, hchild, rfl⟩, hv⟩
      simpa [instantiate] using ih child hchild hchildNot)
    simpa using hmap

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
    instantiate b a = a := by
  induction a with
  | var x => simp [Atom.vars] at h
  | expr xs ih =>
      simp only [Atom.vars] at h
      rw [List.flatten_eq_nil_iff] at h
      simp only [instantiate, Bindings.resolveAtom]
      congr 1
      have hmap : List.map (Bindings.resolveAtom b) xs = List.map id xs :=
        List.map_congr_left (fun child hchild => by
          simpa [instantiate] using
            ih child hchild (h child.vars (List.mem_map_of_mem hchild)))
      simpa using hmap
  | _ => simp [instantiate, Bindings.resolveAtom]

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

/-- Successful recursive binding resolution can only grow an atom. -/
theorem Bindings.resolveAtomAux_size_le (b : Bindings) (fuel : Nat)
    (visited : List VarName) (a resolved : Atom)
    (h : Bindings.resolveAtomAux b fuel visited a = some resolved) :
    a.size ≤ resolved.size := by
  induction fuel generalizing visited a resolved with
  | zero => simp [Bindings.resolveAtomAux] at h
  | succ fuel ih =>
      cases a with
      | var x => simpa [Atom.size] using Atom.one_le_size resolved
      | sym s =>
          simp [Bindings.resolveAtomAux] at h
          subst resolved
          exact Nat.le_refl _
      | gnd g =>
          simp [Bindings.resolveAtomAux] at h
          subst resolved
          exact Nat.le_refl _
      | expr xs =>
          simp only [Bindings.resolveAtomAux] at h
          cases hm : xs.mapM (Bindings.resolveAtomAux b fuel visited) with
          | none => simp [hm] at h
          | some ys =>
              simp [hm] at h
              subst resolved
              simp only [Atom.size, Nat.add_le_add_iff_left]
              have hmap : ∀ (as bs : List Atom),
                  as.mapM (Bindings.resolveAtomAux b fuel visited) = some bs →
                    (as.map Atom.size).sum ≤ (bs.map Atom.size).sum := by
                intro as
                induction as with
                | nil =>
                    intro bs hbs
                    simp at hbs
                    subst bs
                    simp
                | cons head tail iht =>
                    intro bs hbs
                    simp only [List.mapM_cons] at hbs
                    cases hh : Bindings.resolveAtomAux b fuel visited head with
                    | none => simp [hh] at hbs
                    | some head' =>
                        cases ht : tail.mapM (Bindings.resolveAtomAux b fuel visited) with
                        | none => simp [hh, ht] at hbs
                        | some tail' =>
                            simp [hh, ht] at hbs
                            subst bs
                            simp only [List.map_cons, List.sum_cons]
                            exact Nat.add_le_add (ih visited head head' hh) (iht tail' ht)
              exact hmap xs ys hm

/-- `Atom.size` is monotone under equality-class-aware `instantiate`. -/
theorem instantiate_size_le (b : Bindings) (a : Atom) : a.size ≤ (instantiate b a).size := by
  induction a with
  | var x => simp only [instantiate, Bindings.resolveAtom, Atom.size]; exact Atom.one_le_size _
  | expr xs ih =>
      simp only [instantiate, Bindings.resolveAtom, Atom.size]
      have hsum : (xs.map Atom.size).sum ≤
          ((xs.map (Bindings.resolveAtom b)).map Atom.size).sum := by
        rw [List.map_map]
        exact List.sum_le_sum (fun x hx => ih x hx)
      omega
  | _ => simp [instantiate, Bindings.resolveAtom, Atom.size]

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
