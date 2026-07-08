-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.IndexingComplete
Layer: Proofs
Purpose: First-argument rule indexing is sound and complete. The head-k bucket holds exactly the
  =-rules whose left-hand side is headed by k, and varRules holds exactly the head-less rules, so
  every candidate offered for a query is a genuine rule and every rule that could fire is offered.
  Indexing drops no firing rule, the very regime where Hyperon's own Space::visit under-counts (open
  issue 1079). The syntactic half built on top of the semantic head-agreement law from Indexing.lean.
Imports: MettaHyperonFull.Proofs.Indexing
Trusted boundary: none (fully proved)
Main exports: foldl_idx, ruleIndex_getD, ofAtomsGT_varRules, candidates_sound, candidates_complete
Open obligations: none
-/
import MettaHyperonFull.Proofs.Indexing

/-!
# Metatheory: first-argument rule indexing is SOUND and COMPLETE

`MettaHyperonFull/Proofs/Indexing.lean` proves the *semantic* half of Hyperon improvement #9
(`matchAtoms_headKey`: matching forces head agreement). This file proves the *syntactic* half and
the resulting sound-and-complete characterisation.

`MinEnv.ofAtomsGT` indexes the `=`-rules by the head key of their left-hand side:

    MinEnv.candidates env toEval
      = (match headKey toEval with | some k => env.ruleIndex.getD k [] | none => []) ++ env.varRules

`ruleIndex` maps each head symbol to its rules in knowledge-base order, and `varRules` holds the
head-less rules. `candidates toEval` offers the bucket for `toEval`'s head together with `varRules`.

* `ruleIndex_getD`:      the head-`k` bucket is the `=`-rules with a head-`k` LHS (via the
                         `alter`-foldl invariant `foldl_idx`).
* `ofAtomsGT_varRules`:  `varRules` is the head-less rules.
* `candidates_sound`:    every candidate offered is a genuine `=`-rule (`candidates ⊆ extractRules`):
                         indexing never fabricates a rule.
* `candidates_complete`: any rule whose LHS matches a query headed by `k` is a candidate (head-`k`
                         rules from the bucket, head-less ones from `varRules`).
                         Indexing never drops a rule that could fire.

So first-argument indexing is **sound and complete**. Note: Hyperon's own `Space::visit`
under-counts atoms in this same-head regime (open issue #1079); here completeness is a
machine-checked theorem.
-/

namespace Metta
open Metta.Minimal Std

/-- Foldl invariant for the `alter`-based bucket build. The step `f` is a parameter described by
`hf` (so the lemma applies to `ofAtomsGT`'s inline `match`-lambda, which compiles to its own match
auxiliary, by first-order unification of `f`). The `k` bucket accumulates the processed
head-`k` rules, in order, on top of the seed `m0`. -/
theorem foldl_idx (k : String)
    (f : HashMap String (List (Atom × Atom)) → (Atom × Atom) → HashMap String (List (Atom × Atom)))
    (hf : ∀ m lr, f m lr = (match headKey lr.1 with
       | some k' => m.alter k' (fun cur => some ((cur.getD []) ++ [lr]))
       | none => m))
    (rules : List (Atom × Atom)) :
    ∀ (m0 : HashMap String (List (Atom × Atom))),
    (rules.foldl f m0).getD k []
      = m0.getD k [] ++ rules.filter (fun r => headKey r.1 == some k) := by
  induction rules with
  | nil => intro m0; simp
  | cons lr rest ih =>
      intro m0
      rw [List.foldl_cons, hf]
      simp only [List.filter_cons]
      cases hk : headKey lr.1 with
      | none => rw [ih]; simp
      | some k' =>
          by_cases hkk : k' = k
          · subst hkk
            rw [ih, Std.HashMap.getD_alter_self]
            simp [List.append_assoc, Std.HashMap.getD_eq_getD_getElem?]
          · rw [ih, Std.HashMap.getD_alter]
            simp [hkk]

/-- The head-`k` bucket of `ofAtomsGT`'s index is the `=`-rules whose LHS is headed by `k`,
in knowledge-base order. -/
theorem ruleIndex_getD (atoms : List Atom) (gt : GroundingTable) (k : String) :
    (MinEnv.ofAtomsGT atoms gt).ruleIndex.getD k []
      = (extractRules atoms).filter (fun r => headKey r.1 == some k) := by
  dsimp only [MinEnv.ofAtomsGT]
  rw [foldl_idx]
  · simp [extractRules, Std.HashMap.getD_emptyWithCapacity]
  · exact fun _ _ => rfl

/-- The head-less rules of `ofAtomsGT` are the extracted rules with no head key. -/
theorem ofAtomsGT_varRules (atoms : List Atom) (gt : GroundingTable) :
    (MinEnv.ofAtomsGT atoms gt).varRules
      = (extractRules atoms).filter (fun r => (headKey r.1).isNone) := rfl

/-- **Soundness of first-argument indexing.** Every candidate offered for a query is a genuine
`=`-rule of the space (`candidates ⊆ extractRules`): the index never invents a rule. The head-`k`
candidates come from the `k` bucket, the head-less ones from `varRules`; both are sublists of the
extracted rules. -/
theorem candidates_sound (atoms : List Atom) (gt : GroundingTable) (toEval : Atom) (r : Atom × Atom)
    (hr : r ∈ (MinEnv.ofAtomsGT atoms gt).candidates toEval) : r ∈ extractRules atoms := by
  cases hk : headKey toEval with
  | none =>
      simp only [MinEnv.candidates, hk, List.nil_append] at hr
      rw [ofAtomsGT_varRules] at hr
      exact (List.mem_filter.mp hr).1
  | some k =>
      simp only [MinEnv.candidates, hk, List.mem_append] at hr
      rcases hr with h | h
      · rw [ruleIndex_getD] at h; exact (List.mem_filter.mp h).1
      · rw [ofAtomsGT_varRules] at h; exact (List.mem_filter.mp h).1

/-- **Completeness of first-argument indexing.** A rule whose left-hand side matches a query headed
by `k` is always offered as a candidate: head-`k` rules sit in the `k` bucket, head-less rules in
`varRules`, and `candidates` returns both. So indexing never drops a rule that could fire. -/
theorem candidates_complete (atoms : List Atom) (gt : GroundingTable) (toEval : Atom) (k : String)
    (lhs rhs : Atom) (hk : headKey toEval = some k)
    (hr : (lhs, rhs) ∈ extractRules atoms) (hm : matchAtoms lhs toEval ≠ []) :
    (lhs, rhs) ∈ (MinEnv.ofAtomsGT atoms gt).candidates toEval := by
  simp only [MinEnv.candidates, hk]
  rcases matchAtoms_headKey hk hm with hlhs | hlhs
  · refine List.mem_append_left _ ?_
    rw [ruleIndex_getD, List.mem_filter]
    exact ⟨hr, by simp [hlhs]⟩
  · refine List.mem_append_right _ ?_
    rw [ofAtomsGT_varRules, List.mem_filter]
    exact ⟨hr, by simp [hlhs]⟩

end Metta
