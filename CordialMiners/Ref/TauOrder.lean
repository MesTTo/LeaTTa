/-
Module: CordialMiners.Ref.TauOrder
Layer: Ref
Purpose: A concrete, computable deterministic ordering, the executable core of tau_ord (Appendix J).
  It is a Kahn-style topological sort over a finite dependency graph with canonical tie-breaking: at
  each round it emits the least (by the linear order on hashes) item whose dependencies are all already
  emitted, then recurses. Recursion is structural on a fuel counter (the vertex count), so the function
  is total without `partial`. We prove the safety core: determinism (it is a pure function),
  no-duplicates, output-validity (every emitted item came from the input), and topological-sortedness
  (no dependency is ever placed after the item that depends on it).
Imports: CordialMiners.Foundation.Basic
Trusted boundary: none (fully proved)
Main exports: topoSources, topoAux, topoSort, TopoSorted, topoSort_deterministic, topoSort_subset,
  topoSort_nodup, topoSort_topoSorted, topoSort_complete
Open obligations: prefix-monotonicity under leader safety (TAU-08, the OutputMonotone contract of
  Spec.TauOrderSpec) is the leader-safety package, conditional on leader finality.
-/
import CordialMiners.Foundation.Basic

namespace CordialMiners

variable {H : Type*} [LinearOrder H]

/-- The sources of the dependency graph restricted to the still-unemitted set: items whose
    dependencies all lie outside `remaining` (already emitted, or never in the graph). -/
def topoSources (deps : H → Finset H) (remaining : Finset H) : Finset H :=
  remaining.filter (fun x => deps x ∩ remaining = ∅)

/-- A source is one of the unemitted items. -/
theorem topoSources_subset (deps : H → Finset H) (remaining : Finset H) :
    topoSources deps remaining ⊆ remaining := Finset.filter_subset _ _

/-- A source has no dependency left in the unemitted set. -/
theorem topoSources_dep {deps : H → Finset H} {remaining : Finset H} {x : H}
    (hx : x ∈ topoSources deps remaining) : deps x ∩ remaining = ∅ := (Finset.mem_filter.mp hx).2

/-- One round of Kahn's algorithm, driven by a fuel counter. With fuel left and a source available,
    emit the least source and recurse on the rest; otherwise stop. -/
def topoAux (deps : H → Finset H) : ℕ → Finset H → List H
  | 0, _ => []
  | n + 1, remaining =>
      if h : (topoSources deps remaining).Nonempty then
        (topoSources deps remaining).min' h ::
          topoAux deps n (remaining.erase ((topoSources deps remaining).min' h))
      else []

/-- The concrete ordering: run the topological sort with fuel equal to the vertex count. -/
def topoSort (V : Finset H) (deps : H → Finset H) : List H := topoAux deps V.card V

/-- A list is topologically sorted for `deps` when no item's dependency appears after it: for every
    way of splitting the list at an item `y`, none of `y`'s dependencies sit in the tail. -/
def TopoSorted (deps : H → Finset H) (L : List H) : Prop :=
  ∀ l₁ y l₂, L = l₁ ++ y :: l₂ → ∀ p ∈ deps y, p ∉ l₂

/-- Every emitted item was in the working set it was drawn from. -/
theorem topoAux_mem (deps : H → Finset H) (n : ℕ) :
    ∀ (remaining : Finset H) {y : H}, y ∈ topoAux deps n remaining → y ∈ remaining := by
  induction n with
  | zero => intro remaining y hy; simp [topoAux] at hy
  | succ n ih =>
    intro remaining y hy
    simp only [topoAux] at hy
    split at hy
    · rename_i h
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact topoSources_subset deps remaining (Finset.min'_mem _ h)
      · exact Finset.mem_of_mem_erase (ih _ hy')
    · simp at hy

/-- The output has no duplicates: each emitted item is erased from the working set, so it can never be
    picked again. -/
theorem topoAux_nodup (deps : H → Finset H) (n : ℕ) :
    ∀ remaining : Finset H, (topoAux deps n remaining).Nodup := by
  induction n with
  | zero => intro remaining; simp [topoAux]
  | succ n ih =>
    intro remaining
    simp only [topoAux]
    split
    · rename_i h
      rw [List.nodup_cons]
      refine ⟨fun hmem => ?_, ih _⟩
      exact Finset.notMem_erase _ _ (topoAux_mem deps n _ hmem)
    · simp

/-- The output respects dependencies: an item is emitted only when all its remaining dependencies are
    gone, so no dependency of an item ever appears after it. -/
theorem topoAux_topoSorted (deps : H → Finset H) (n : ℕ) :
    ∀ remaining : Finset H, TopoSorted deps (topoAux deps n remaining) := by
  induction n with
  | zero => intro remaining l₁ y l₂ heq p hp; simp [topoAux] at heq
  | succ n ih =>
    intro remaining l₁ y l₂ heq p hp
    simp only [topoAux] at heq
    split at heq
    · rename_i h
      have hdisj : deps ((topoSources deps remaining).min' h) ∩ remaining = ∅ :=
        topoSources_dep (Finset.min'_mem _ h)
      cases l₁ with
      | nil =>
        rw [List.nil_append] at heq
        injection heq with h1 h2
        subst h1; subst h2
        intro hpl2
        have hprem : p ∈ remaining := Finset.mem_of_mem_erase (topoAux_mem deps n _ hpl2)
        have hpd : p ∈ deps ((topoSources deps remaining).min' h) ∩ remaining :=
          Finset.mem_inter.mpr ⟨hp, hprem⟩
        rw [hdisj] at hpd
        simp at hpd
      | cons a l₁' =>
        rw [List.cons_append] at heq
        injection heq with h1 h2
        subst h1
        exact ih _ l₁' y l₂ h2 p hp
    · simp at heq

/-- TAU-04 realized concretely: the ordering is a pure function, so equal inputs give equal outputs. -/
theorem topoSort_deterministic (V₁ V₂ : Finset H) (deps : H → Finset H) (h : V₁ = V₂) :
    topoSort V₁ deps = topoSort V₂ deps := by rw [h]

/-- Output-validity: every hash in the ordered output came from the input vertex set. -/
theorem topoSort_subset (V : Finset H) (deps : H → Finset H) {y : H} (hy : y ∈ topoSort V deps) :
    y ∈ V := topoAux_mem deps V.card V hy

/-- The ordered output has no duplicate positions. -/
theorem topoSort_nodup (V : Finset H) (deps : H → Finset H) : (topoSort V deps).Nodup :=
  topoAux_nodup deps V.card V

/-- The ordered output is topologically sorted: no dependency is ever placed after the item that
    depends on it. This is the causal-consistency guarantee of the deterministic ordering. -/
theorem topoSort_topoSorted (V : Finset H) (deps : H → Finset H) :
    TopoSorted deps (topoSort V deps) := topoAux_topoSorted deps V.card V

/-- Under a strict rank (every dependency has smaller rank, so the graph is acyclic) a nonempty
    working set always has a source: the element of least rank, whose dependencies all rank below it
    and so cannot still be in the working set. -/
theorem topoSources_nonempty_of_rank (deps : H → Finset H) {rank : H → ℕ}
    (hrank : ∀ x, ∀ p ∈ deps x, rank p < rank x) {remaining : Finset H} (hne : remaining.Nonempty) :
    (topoSources deps remaining).Nonempty := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image remaining rank hne
  refine ⟨x, ?_⟩
  simp only [topoSources, Finset.mem_filter]
  refine ⟨hx, Finset.eq_empty_of_forall_notMem (fun p hp => ?_)⟩
  rw [Finset.mem_inter] at hp
  have h1 := hrank x p hp.1
  have h2 := hmin p hp.2
  omega

/-- Completeness under a strict rank: with fuel at least the working-set size, every item is emitted.
    Acyclicity gives a source at every nonempty round, so the fuel is never exhausted early. -/
theorem topoAux_complete (deps : H → Finset H) {rank : H → ℕ}
    (hrank : ∀ x, ∀ p ∈ deps x, rank p < rank x) :
    ∀ (n : ℕ) (remaining : Finset H), remaining.card ≤ n →
      ∀ {y : H}, y ∈ remaining → y ∈ topoAux deps n remaining := by
  intro n
  induction n with
  | zero =>
    intro remaining hcard y hy
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    subst hcard
    simp at hy
  | succ n ih =>
    intro remaining hcard y hy
    have hcond := topoSources_nonempty_of_rank deps hrank ⟨y, hy⟩
    simp only [topoAux]
    split
    · rename_i h
      by_cases hyx : y = (topoSources deps remaining).min' h
      · rw [hyx]; simp
      · apply List.mem_cons_of_mem
        refine ih (remaining.erase _) ?_ (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        rw [Finset.card_erase_of_mem (topoSources_subset deps remaining (Finset.min'_mem _ h))]
        omega
    · rename_i h
      exact absurd hcond h

/-- TAU completeness: every input vertex appears in the ordered output (under acyclicity). Together
    with topoSort_subset and topoSort_nodup, the output lists exactly the input vertices, once each. -/
theorem topoSort_complete (V : Finset H) (deps : H → Finset H) {rank : H → ℕ}
    (hrank : ∀ x, ∀ p ∈ deps x, rank p < rank x) {y : H} (hy : y ∈ V) : y ∈ topoSort V deps :=
  topoAux_complete deps hrank V.card V (le_refl _) hy

end CordialMiners
