-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.CaptureAvoidingFreshening
Layer: Proofs
Purpose: Avoidance, injectivity, compatibility, and regression theorems for the minimal
  interpreter's finite capture-avoiding freshener.
Imports: MettaHyperonFull.Proofs.BindingLaws
Trusted boundary: none
Main exports: captureAvoidingName_not_mem, captureAvoidingName_injective,
  freshenRuleAvoiding_counter, freshenRuleAvoiding_eq_legacy,
  freshenRuleAvoiding_vars_fresh, legacyFreshening_capture_drops_candidate_canary
Open obligations: none
-/
import MettaHyperonFull.Proofs.BindingLaws

namespace Metta.Minimal
open Metta

private theorem length_le_sum_lengths_of_mem
    {s : String} {names : List String} (h : s ∈ names) :
    s.length ≤ (names.map String.length).sum := by
  induction names with
  | nil => simp at h
  | cons name names ih =>
      simp only [List.mem_cons] at h
      simp only [List.map_cons, List.sum_cons]
      rcases h with rfl | h
      · omega
      · have := ih h
        omega

/-- Every fallback spelling is outside the finite avoid set. -/
theorem captureAvoidingName_not_mem
    (avoid : List VarName) (counter : Nat) (v : VarName) :
    captureAvoidingName avoid counter v ∉ avoid := by
  intro hmem
  have hle := length_le_sum_lengths_of_mem hmem
  have hprefix : (avoidancePrefix avoid).length = (avoid.map String.length).sum + 1 := by
    simp [avoidancePrefix]
  have hout : (avoid.map String.length).sum + 1 ≤
      (captureAvoidingName avoid counter v).length := by
    simp [captureAvoidingName, String.length_append, hprefix]
    omega
  omega

/-- Fallback renaming cannot identify two distinct source variables. -/
theorem captureAvoidingName_injective (avoid : List VarName) (counter : Nat) :
    Function.Injective (captureAvoidingName avoid counter) := by
  intro left right h
  have h' : avoidancePrefix avoid ++ (left ++ ("#" ++ toString counter)) =
      avoidancePrefix avoid ++ (right ++ ("#" ++ toString counter)) := by
    simpa [captureAvoidingName, String.append_assoc] using h
  have h'' : left ++ ("#" ++ toString counter) =
      right ++ ("#" ++ toString counter) :=
    (String.append_right_inj (avoidancePrefix avoid)).mp h'
  exact (String.append_left_inj ("#" ++ toString counter)).mp h''

theorem renameAllVars_avoids
    (avoid : List VarName) (f : VarName → VarName)
    (hf : ∀ v, f v ∉ avoid) (a : Atom) :
    ∀ v ∈ (renameAllVars f a).vars, v ∉ avoid := by
  cases a with
  | sym s => simp [renameAllVars, Atom.vars]
  | var name => simpa [renameAllVars, Atom.vars] using hf name
  | gnd g => simp [renameAllVars, Atom.vars]
  | expr xs =>
      intro v hv
      simp only [renameAllVars, Atom.vars, List.map_map] at hv
      rcases List.mem_flatten.mp hv with ⟨vs, hvs, hv⟩
      rcases List.mem_map.mp hvs with ⟨x, hx, hvars⟩
      rw [← hvars] at hv
      exact renameAllVars_avoids avoid f hf x v hv
termination_by a.size
decreasing_by
  have hmem : x.size ∈ xs.map Atom.size := List.mem_map_of_mem hx
  have hle := List.single_le_sum (fun _ _ => Nat.zero_le _) x.size hmem
  simpa [Atom.size, Nat.add_comm] using Nat.lt_succ_of_le hle

/-- Freshening advances the counter by exactly one, including on the collision fallback. -/
theorem freshenRuleAvoiding_counter
    (counter : Nat) (avoid : List VarName) (lhs rhs : Atom) :
    (freshenRuleAvoiding counter avoid lhs rhs).2 = counter + 1 := by
  by_cases h : ∃ v ∈ (freshenRule counter lhs rhs).1.vars ++
      (freshenRule counter lhs rhs).2.vars, v ∈ avoid
  · rw [freshenRuleAvoiding, if_pos h]
  · rw [freshenRuleAvoiding, if_neg h]

/-- Compatibility branch: when the legacy spelling is already disjoint, the repaired operation
returns that exact alpha-renaming and advances the counter once. -/
theorem freshenRuleAvoiding_eq_legacy
    (counter : Nat) (avoid : List VarName) (lhs rhs : Atom)
    (hsafe : ¬ ∃ v ∈ (freshenRule counter lhs rhs).1.vars ++
        (freshenRule counter lhs rhs).2.vars, v ∈ avoid) :
    freshenRuleAvoiding counter avoid lhs rhs =
      (freshenRule counter lhs rhs, counter + 1) := by
  rw [freshenRuleAvoiding, if_neg hsafe]

/-- The avoidance contract: no variable in either renamed rule side has a spelling in `avoid`. -/
theorem freshenRuleAvoiding_vars_fresh
    (counter : Nat) (avoid : List VarName) (lhs rhs : Atom) :
    ∀ v ∈ (freshenRuleAvoiding counter avoid lhs rhs).1.1.vars ++
        (freshenRuleAvoiding counter avoid lhs rhs).1.2.vars,
      v ∉ avoid := by
  unfold freshenRuleAvoiding
  dsimp only
  split
  · rename_i hcollision
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with hv | hv
    · exact renameAllVars_avoids avoid (captureAvoidingName avoid counter)
        (captureAvoidingName_not_mem avoid counter) lhs v hv
    · exact renameAllVars_avoids avoid (captureAvoidingName avoid counter)
        (captureAvoidingName_not_mem avoid counter) rhs v hv
  · rename_i hsafe
    intro v hv hmem
    exact hsafe ⟨v, hv, hmem⟩

/-! The following two canaries expose the capability change directly. The first records the old
counter-suffix collision; the second requires the repaired operation to reject that visible name. -/

private def freshnessCollisionPattern : Atom :=
  .expr [.sym "f", .var "x"]

private def freshnessCollisionIncoming : Bindings :=
  [BindingRel.val "x#0" (.sym "b")]

private def freshnessCollisionQuery : Atom :=
  .expr [.sym "f", .sym "a"]

/-- The candidate operation used before capture-avoiding freshening was introduced. Kept locally so
the negative canary states the former runtime failure without keeping that behavior in production. -/
private def legacyQueryOpItemsOfRule (prev : Stack) (toEval : Atom)
    (b : Bindings) (counter : Nat) (p : Atom × Atom) : List Item :=
  let (lhs', rhs') := freshenRule counter p.1 p.2
  (matchAtoms lhs' toEval).flatMap fun mb =>
    (Bindings.merge b mb).filterMap fun m =>
      if Bindings.hasLoop m then none
      else some (evalResult prev (instantiate m rhs') m)

theorem legacyFreshening_collision_canary :
    ∃ v ∈ (freshenRule 0 freshnessCollisionPattern (.var "x")).1.vars ++
        (freshenRule 0 freshnessCollisionPattern (.var "x")).2.vars,
      v ∈ ["x#0"] := by
  refine ⟨"x#0", ?_, by simp⟩
  have hzero : Nat.repr 0 = "0" := by decide
  simp [freshnessCollisionPattern, freshenRule, Atom.vars, Subst.apply, Subst.lookup, hzero]

/-- The legacy freshener assigns the rule variable exactly the live incoming spelling at counter
zero. -/
theorem legacyFreshening_collision_exact :
    (freshenRule 0 freshnessCollisionPattern (.var "x")).1 =
      .expr [.sym "f", .var "x#0"] := by
  have hzero : Nat.repr 0 = "0" := by decide
  simp [freshnessCollisionPattern, freshenRule, Atom.vars,
    Subst.apply, Subst.lookup, hzero]

/-- With the legacy spelling, matching the candidate attempts to overwrite the incoming variable. -/
theorem legacyFreshening_capture_match_canary :
    matchAtoms (freshenRule 0 freshnessCollisionPattern (.var "x")).1
        freshnessCollisionQuery =
      [[BindingRel.val "x#0" (.sym "a")]] := by
  rw [legacyFreshening_collision_exact]
  have hclass : Bindings.classValues ([] : Bindings) "x#0" = [] := by
    simp [Bindings.classValues, Bindings.lookupVal]
  have hadd :
      Bindings.addVarBinding [] "x#0" (.sym "a") =
        [[BindingRel.val "x#0" (.sym "a")]] := by
    simpa [Bindings.addValRaw, Bindings.removeVal] using
      (Bindings.addVarBinding_fresh hclass (by intro name h; cases h))
  have hraw :
      matchAtomsWith none
          (.expr [.sym "f", .var "x#0"])
          freshnessCollisionQuery =
        [[BindingRel.val "x#0" (.sym "a")]] := by
    simp only [freshnessCollisionQuery, matchAtomsWith]
    unfold matchAll
    simp [matchAtomsWith, Bindings.merge]
    unfold matchAll
    simp [matchAtomsWith, Bindings.merge]
    unfold matchAll
    have hloop :
        Bindings.hasLoop [BindingRel.val "x#0" (.sym "a")] = false :=
      Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Atom.vars])
    simp [Subst.occurs, hloop, Bindings.mergeOne, hadd]
  rw [matchAtoms, hraw]
  simp [Bindings.hasLoop_singleton_val_of_not_mem, Atom.vars]

/-- The captured match conflicts with the already-live value of the same spelling. -/
theorem legacyFreshening_capture_merge_conflict_canary :
    Bindings.merge freshnessCollisionIncoming
      [BindingRel.val "x#0" (.sym "a")] = [] := by
  have hvalues :
      Bindings.classValues freshnessCollisionIncoming "x#0" = [.sym "b"] := by
    simp [freshnessCollisionIncoming, Bindings.classValues,
      Bindings.eqClassOrdered, Bindings.eqVarsInOrder, Bindings.lookupVal]
  have hunify :
      Bindings.unifyValues ([.sym "b"] ++ [.sym "a"]) = none := by
    simp [Bindings.unifyValues, Unify.unifyRounds,
      Unify.decomposeAll, Unify.decomposeEq, Atom.size]
  have hadd :
      Bindings.addVarBinding freshnessCollisionIncoming "x#0" (.sym "a") = [] :=
    Bindings.addVarBinding_conflict
      (by intro name h; cases h) hvalues (by simp) hunify
  simpa [Bindings.merge, Bindings.mergeOne] using hadd

/-- Semantic negative canary: the formerly executable candidate operation drops a valid rule solely
because counter-based freshening captures a reachable incoming variable spelling. -/
theorem legacyFreshening_capture_drops_candidate_canary :
    legacyQueryOpItemsOfRule [] freshnessCollisionQuery freshnessCollisionIncoming 0
        (freshnessCollisionPattern, .var "x") = [] := by
  simp [legacyQueryOpItemsOfRule, legacyFreshening_capture_match_canary,
    legacyFreshening_capture_merge_conflict_canary]

/-- The colliding incoming state is produced by the ordinary counter-zero evaluator path; it is not
an artificial binding set excluded by the runtime. -/
theorem legacyFreshening_capture_incoming_reachable_canary :
    unifyOp [] (.sym "b") (.var "x#0") (.sym "ok") (.sym "fallback") [] =
      [finItem [] (.sym "ok") freshnessCollisionIncoming] := by
  have hloop :
      Bindings.hasLoop [BindingRel.val "x#0" (.sym "b")] = false :=
    Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Atom.vars])
  have hmatch :
      matchAtoms (.sym "b") (.var "x#0") =
        [[BindingRel.val "x#0" (.sym "b")]] := by
    simp [matchAtoms, matchAtomsWith, Subst.occurs, hloop]
  have hmerge :
      Bindings.merge [] [BindingRel.val "x#0" (.sym "b")] =
        [[BindingRel.val "x#0" (.sym "b")]] := by
    simp [Bindings.merge, Bindings.mergeOne,
      Bindings.addVarBinding_fresh, Bindings.classValues,
      Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal]
  simp [unifyOp, hmatch, hmerge, hloop, freshnessCollisionIncoming,
    instantiate, Bindings.resolveAtom]

theorem captureAvoidingFreshening_rejects_visible_collision_canary :
    ∀ v ∈ (freshenRuleAvoiding 0 ["x#0"] freshnessCollisionPattern (.var "x")).1.1.vars ++
        (freshenRuleAvoiding 0 ["x#0"] freshnessCollisionPattern (.var "x")).1.2.vars,
      v ∉ ["x#0"] :=
  freshenRuleAvoiding_vars_fresh 0 ["x#0"] freshnessCollisionPattern (.var "x")

end Metta.Minimal
