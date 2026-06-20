/-
Module: MeTTaILProofs.Lattice
Layer: Proofs
Purpose: The presentation lattice laws. Union, intersection, and difference behave as set operations
  on each component of a presentation. The three operators in `MeTTaIL.Theory.Ops` build their five
  components with `distinct`, `List.filter`, and `List.contains`, so we characterize membership in
  the result component by component. The key lemma is `mem_distinct`: `distinct` keeps exactly the
  elements it was given. For intersection and difference the term, equation, and rewrite components
  carry survival side conditions, so there we prove the implication into the inputs; the exports
  component has no side condition, so there the full `↔` holds.
Imports: MeTTaIL.Theory.Ops, MeTTaILProofs.DecEq
Trusted boundary: none (fully proved)
Main exports: mem_distinct, distinct_nodup; the membership characterizations mem_union_*,
  mem_inter_*, mem_diff_*; the corollaries mem_union_exports_comm, mem_union_exports_self.
Open obligations: none
-/
import MeTTaIL.Theory.Ops
import MeTTaILProofs.DecEq

namespace MeTTaIL

open List

/-! ### The core lemma: `distinct` preserves membership -/

/-- Membership through the `distinct` fold, stated for an arbitrary starting accumulator. An element
    is in `xs.foldl (keep-first) acc` exactly when it was already in `acc` or it occurs in `xs`. We
    generalize over `acc` so the induction on `xs` goes through. -/
theorem mem_distinct_foldl {α : Type} [BEq α] [LawfulBEq α] (x : α) :
    ∀ (xs acc : List α),
      x ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc
        ↔ x ∈ acc ∨ x ∈ xs
  | [], acc => by simp
  | y :: ys, acc => by
      simp only [List.foldl_cons]
      rw [mem_distinct_foldl x ys]
      by_cases h : acc.contains y
      · -- `y` already present, so the accumulator is unchanged.
        have hy : y ∈ acc := by simpa using h
        rw [if_pos h]
        constructor
        · rintro (hacc | hys)
          · exact Or.inl hacc
          · exact Or.inr (List.mem_cons_of_mem _ hys)
        · rintro (hacc | hcons)
          · exact Or.inl hacc
          · rcases List.mem_cons.1 hcons with rfl | hys
            · exact Or.inl hy
            · exact Or.inr hys
      · -- `y` is new, so it gets appended to the accumulator.
        rw [if_neg h]
        rw [List.mem_append]
        constructor
        · rintro ((hacc | hsingle) | hys)
          · exact Or.inl hacc
          · exact Or.inr (List.mem_cons.2 (Or.inl (by simpa using hsingle)))
          · exact Or.inr (List.mem_cons_of_mem _ hys)
        · rintro (hacc | hcons)
          · exact Or.inl (Or.inl hacc)
          · rcases List.mem_cons.1 hcons with rfl | hys
            · exact Or.inl (Or.inr (List.mem_singleton.2 rfl))
            · exact Or.inr hys

/-- `distinct` keeps exactly the elements it was given. -/
theorem mem_distinct {α : Type} [BEq α] [LawfulBEq α] {x : α} {xs : List α} :
    x ∈ distinct xs ↔ x ∈ xs := by
  unfold distinct
  rw [mem_distinct_foldl x xs []]
  simp

/-! ### `distinct` produces no duplicates -/

/-- The `distinct` fold keeps the accumulator duplicate-free, stated for an arbitrary starting
    accumulator that is already duplicate-free. -/
theorem nodup_distinct_foldl {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs acc : List α), acc.Nodup →
      (xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).Nodup
  | [], acc, h => by simpa using h
  | y :: ys, acc, h => by
      simp only [List.foldl_cons]
      by_cases hy : acc.contains y
      · rw [if_pos hy]
        exact nodup_distinct_foldl ys acc h
      · rw [if_neg hy]
        have hmem : y ∉ acc := by simpa using hy
        have happ : (acc ++ [y]).Nodup := by
          rw [List.nodup_append]
          refine ⟨h, List.nodup_singleton y, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          exact fun hab => hmem (hab ▸ ha)
        exact nodup_distinct_foldl ys (acc ++ [y]) happ

/-- The result of `distinct` has no duplicates. -/
theorem distinct_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    (distinct xs).Nodup := by
  unfold distinct
  exact nodup_distinct_foldl xs [] List.nodup_nil

/-! ### Union: each component is the union of the inputs' components

    `Presentation.union` builds every component as `distinct (pa.comp ++ pb.comp)`, so membership in
    the result is just membership in either input, by `mem_distinct` and `List.mem_append`. -/

theorem mem_union_exports {pa pb : Presentation} {c : Cat} :
    c ∈ (Presentation.union pa pb).exports ↔ c ∈ pa.exports ∨ c ∈ pb.exports := by
  cases pa; cases pb
  simp only [Presentation.union, Presentation.exports]
  rw [mem_distinct, List.mem_append]

theorem mem_union_terms {pa pb : Presentation} {r : Rule} :
    r ∈ (Presentation.union pa pb).terms ↔ r ∈ pa.terms ∨ r ∈ pb.terms := by
  cases pa; cases pb
  simp only [Presentation.union, Presentation.terms]
  rw [mem_distinct, List.mem_append]

theorem mem_union_equations {pa pb : Presentation} {e : Equation} :
    e ∈ (Presentation.union pa pb).equations ↔ e ∈ pa.equations ∨ e ∈ pb.equations := by
  cases pa; cases pb
  simp only [Presentation.union, Presentation.equations]
  rw [mem_distinct, List.mem_append]

theorem mem_union_rewrites {pa pb : Presentation} {d : RewriteDecl} :
    d ∈ (Presentation.union pa pb).rewrites ↔ d ∈ pa.rewrites ∨ d ∈ pb.rewrites := by
  cases pa; cases pb
  simp only [Presentation.union, Presentation.rewrites]
  rw [mem_distinct, List.mem_append]

/-! ### Intersection

    The exports of an intersection are the common sorts, with no side condition, so we get the full
    `↔`. The term, equation, and rewrite components apply a further filter (mentioned categories must
    be common, labels must survive), so there we prove the implication into both inputs. -/

theorem mem_inter_exports {pa pb : Presentation} {c : Cat} :
    c ∈ (Presentation.inter pa pb).exports ↔ c ∈ pa.exports ∧ c ∈ pb.exports := by
  cases pa; cases pb
  simp only [Presentation.inter, Presentation.exports, List.mem_filter]
  rw [List.contains_eq_mem, decide_eq_true_iff]

theorem mem_inter_terms {pa pb : Presentation} {r : Rule} :
    r ∈ (Presentation.inter pa pb).terms → r ∈ pa.terms ∧ r ∈ pb.terms := by
  cases pa; cases pb
  simp only [Presentation.inter, Presentation.terms, List.mem_filter]
  rintro ⟨⟨hpa, hpb⟩, _⟩
  rw [List.contains_eq_mem, decide_eq_true_iff] at hpb
  exact ⟨hpa, hpb⟩

theorem mem_inter_equations {pa pb : Presentation} {e : Equation} :
    e ∈ (Presentation.inter pa pb).equations → e ∈ pa.equations ∧ e ∈ pb.equations := by
  cases pa; cases pb
  simp only [Presentation.inter, Presentation.equations, List.mem_filter]
  rintro ⟨⟨hpa, hpb⟩, _⟩
  rw [List.contains_eq_mem, decide_eq_true_iff] at hpb
  exact ⟨hpa, hpb⟩

theorem mem_inter_rewrites {pa pb : Presentation} {d : RewriteDecl} :
    d ∈ (Presentation.inter pa pb).rewrites → d ∈ pa.rewrites ∧ d ∈ pb.rewrites := by
  cases pa; cases pb
  simp only [Presentation.inter, Presentation.rewrites, List.mem_filter]
  rintro ⟨⟨hpa, hpb⟩, _⟩
  rw [List.contains_eq_mem, decide_eq_true_iff] at hpb
  exact ⟨hpa, hpb⟩

/-! ### Difference

    The exports of a difference are `pa`'s sorts that are not in `pb`, with no side condition, so we
    get the full `↔`. The other three components carry the survival filter, so there we prove the
    implication into "in `pa` and not in `pb`". -/

theorem mem_diff_exports {pa pb : Presentation} {c : Cat} :
    c ∈ (Presentation.diff pa pb).exports ↔ c ∈ pa.exports ∧ c ∉ pb.exports := by
  cases pa; cases pb
  simp only [Presentation.diff, Presentation.exports, List.mem_filter]
  rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]

theorem mem_diff_terms {pa pb : Presentation} {r : Rule} :
    r ∈ (Presentation.diff pa pb).terms → r ∈ pa.terms ∧ r ∉ pb.terms := by
  cases pa; cases pb
  simp only [Presentation.diff, Presentation.terms, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true']
  rintro ⟨hpa, hpb, _⟩
  rw [List.contains_eq_mem, decide_eq_false_iff_not] at hpb
  exact ⟨hpa, hpb⟩

theorem mem_diff_equations {pa pb : Presentation} {e : Equation} :
    e ∈ (Presentation.diff pa pb).equations → e ∈ pa.equations ∧ e ∉ pb.equations := by
  cases pa; cases pb
  simp only [Presentation.diff, Presentation.equations, List.mem_filter]
  rintro ⟨⟨hpa, hpb⟩, _⟩
  rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hpb
  exact ⟨hpa, hpb⟩

theorem mem_diff_rewrites {pa pb : Presentation} {d : RewriteDecl} :
    d ∈ (Presentation.diff pa pb).rewrites → d ∈ pa.rewrites ∧ d ∉ pb.rewrites := by
  cases pa; cases pb
  simp only [Presentation.diff, Presentation.rewrites, List.mem_filter]
  rintro ⟨⟨hpa, hpb⟩, _⟩
  rw [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hpb
  exact ⟨hpa, hpb⟩

/-! ### Corollaries: union is commutative and idempotent up to membership -/

/-- Up to membership, union of exports is commutative. -/
theorem mem_union_exports_comm {pa pb : Presentation} {c : Cat} :
    c ∈ (Presentation.union pa pb).exports ↔ c ∈ (Presentation.union pb pa).exports := by
  rw [mem_union_exports, mem_union_exports, Or.comm]

/-- Up to membership, union of exports is idempotent. -/
theorem mem_union_exports_self {p : Presentation} {c : Cat} :
    c ∈ (Presentation.union p p).exports ↔ c ∈ p.exports := by
  rw [mem_union_exports, or_self]

end MeTTaIL
