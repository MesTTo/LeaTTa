-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.Sim.Run
Layer: Sim
Purpose: An executable end-to-end run of the protocol pipeline, chaining the verified pieces. For each
  candidate block we fold its approvals through the weighted collector to decide finality, keep the
  finalized blocks, then order them with the verified topological sort. The result is the published
  ordered prefix. This is the integrated protocol as a single computable function, with a worked demo.
Imports: CordialMiners.Ref.WeightedCollector, CordialMiners.Ref.TauOrder
Trusted boundary: none
Main exports: SimInput, finalizes, simulate, demo
Open obligations: none
-/
import CordialMiners.Ref.WeightedCollector
import CordialMiners.Ref.TauOrder

namespace CordialMiners.Sim
open CordialMiners

/-- A simulation scenario: the committee snapshot, the parent-dependency graph on block hashes, the
    candidate blocks, and, per block, the list of approval events (the approving members in arrival
    order). -/
structure SimInput where
  snapshot : CommitteeSnapshot Nat
  deps : Nat → Finset Nat
  candidates : List Nat
  approvals : Nat → List Nat

/-- A block is finalized when folding its approvals through the weighted collector closes the
    certificate (the threshold is crossed). -/
def finalizes (inp : SimInput) (block : Nat) : Bool :=
  ((inp.approvals block).foldl (collectorStep inp.snapshot (fun _ => true)) WCertState.init).done

/-- The integrated pipeline: keep the finalized candidates, then order them with the verified
    topological sort. The output is the published ordered prefix of finalized block hashes. -/
def simulate (inp : SimInput) : List Nat :=
  topoSort (inp.candidates.filter (finalizes inp)).toFinset inp.deps

/-- A worked scenario: three equal-weight members, simple-majority finality, and four candidate blocks
    where 2 and 3 depend on 1 and 4 depends on 2 and 3. Blocks 1, 2, 3 each get two approvals (final);
    the leaf block 4 gets one (not final), so it is dropped. -/
def demo : SimInput where
  snapshot := ⟨{1, 2, 3}, fun _ => 1, 3, ⟨1, 2, by decide⟩⟩
  deps := fun
    | 2 => {1}
    | 3 => {1}
    | 4 => {2, 3}
    | _ => {}
  candidates := [1, 2, 3, 4]
  approvals := fun
    | 1 => [1, 2]
    | 2 => [1, 2]
    | 3 => [1, 2]
    | 4 => [1]
    | _ => []

#eval simulate demo   -- [1, 2, 3]

/-- The integrated run orders the three finalized blocks and drops the non-final leaf. -/
example : simulate demo = [1, 2, 3] := by decide

/-- Blocks 1, 2, 3 finalize on two approvals; block 4 does not on one. -/
example : finalizes demo 3 = true := by decide
example : finalizes demo 4 = false := by decide

end CordialMiners.Sim
