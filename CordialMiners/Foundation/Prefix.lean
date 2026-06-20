/-
Module: CordialMiners.Foundation.Prefix
Layer: Foundation
Purpose: Sequence-prefix theory for ordered consensus output. The deterministic ordering function
  must only ever extend the previously published prefix (the output-prefix discipline, IC10), and two
  correct miners whose outputs are prefixes of a common limit ordering must never disagree. Both rest
  on the prefix order being a partial order with comparable common prefixes. Built on Mathlib's
  `List.IsPrefix` (notation `<+:`).
Imports: CordialMiners.Foundation.Basic
Trusted boundary: none
Main exports: found_08_prefix_refl, found_08_prefix_trans, found_08_prefix_antisymm,
  found_08_prefix_comparable
Open obligations: none
-/
import CordialMiners.Foundation.Basic

namespace CordialMiners

variable {α : Type*}

/-- FOUND-08 (reflexivity): every sequence is a prefix of itself. -/
theorem found_08_prefix_refl (l : List α) : l <+: l := List.prefix_refl l

/-- FOUND-08 (transitivity): prefix composes. -/
theorem found_08_prefix_trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+: l₂) (h₂ : l₂ <+: l₃) :
    l₁ <+: l₃ := h₁.trans h₂

/-- FOUND-08 (antisymmetry up to equality): mutual prefixes are equal. Proved from lengths so it does
    not depend on the exact name of a core antisymmetry lemma. -/
theorem found_08_prefix_antisymm {l₁ l₂ : List α} (h₁ : l₁ <+: l₂) (h₂ : l₂ <+: l₁) :
    l₁ = l₂ := by
  obtain ⟨t, rfl⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  have hlen := congrArg List.length hs
  simp only [List.length_append] at hlen
  have ht : t = [] := by
    rcases t with _ | ⟨a, t'⟩
    · rfl
    · simp only [List.length_cons] at hlen; omega
  subst ht
  simp

/-- FOUND-08 (comparability): two prefixes of a common sequence are themselves prefix-comparable. This
    is the core of output stability: if two correct miners' ordered outputs are each a prefix of the
    same limit ordering, then one output is a prefix of the other, so they never disagree on a
    published position. -/
theorem found_08_prefix_comparable {l₁ l₂ l : List α} (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) :
    l₁ <+: l₂ ∨ l₂ <+: l₁ := List.prefix_or_prefix_of_prefix h₁ h₂

end CordialMiners
