/-
Module: CordialMiners.Tests.Examples
Layer: Tests
Purpose: Worked examples that run the computable core and check the answers at build time. Each example
  is a kernel-checked assertion (via decide), so these double as regression tests and as a demonstration
  that the formalization computes, not just typechecks. The matching #eval lines print the same results.
Imports: CordialMiners.Ref.TauOrder, CordialMiners.Ref.WeightedCollector, CordialMiners.Spec.SchedulerSpec
Trusted boundary: none
Main exports: sampleDeps, sampleSnapshot (test fixtures)
Open obligations: none
-/
import CordialMiners.Ref.TauOrder
import CordialMiners.Ref.WeightedCollector
import CordialMiners.Spec.SchedulerSpec
import CordialMiners.Extract.MettaIL

namespace CordialMiners.Tests
open CordialMiners

/-- A small dependency graph: 2 and 3 each depend on 1, and 4 depends on both 2 and 3. -/
def sampleDeps : Nat → Finset Nat
  | 2 => {1}
  | 3 => {1}
  | 4 => {2, 3}
  | _ => {}

#eval topoSort ({1, 2, 3, 4} : Finset Nat) sampleDeps   -- [1, 2, 3, 4]

/-- The output is the canonical topological order: parents before children, least-first at ties. -/
example : topoSort ({1, 2, 3, 4} : Finset Nat) sampleDeps = [1, 2, 3, 4] := by decide

/-- Tie-breaking is by the linear order: two independent sources come out least-first. -/
example : topoSort ({5, 6} : Finset Nat) (fun _ => (∅ : Finset Nat)) = [5, 6] := by decide

/-- The computed order has no duplicates (a concrete instance of topoSort_nodup). -/
example : (topoSort ({1, 2, 3, 4} : Finset Nat) sampleDeps).Nodup := by decide

/-- A simple-majority threshold (1/2 of total weight 3) is crossed at weight 2 but not at weight 1. -/
example : thresholdPassedBool 2 3 ⟨1, 2, by decide⟩ = true := by decide
example : thresholdPassedBool 1 3 ⟨1, 2, by decide⟩ = false := by decide

/-- The weight of a uniform unit-weight set is its size. -/
example : wt (fun _ => 1) ({1, 2, 3} : Finset Nat) = 3 := by decide

/-- A test snapshot: three equal-weight members and a simple-majority threshold. -/
def sampleSnapshot : CommitteeSnapshot Nat := ⟨{1, 2, 3}, fun _ => 1, 3, ⟨1, 2, by decide⟩⟩

#eval ([1, 2, 3].foldl (collectorStep sampleSnapshot (fun _ => true)) WCertState.init).accWeight  -- 2

/-- Feeding approvals from 1, 2, 3 in order: the certificate closes at the second approval (weight 2
    crosses the majority of total 3), and the third approval is ignored because the collector is
    one-shot. -/
example :
    ([1, 2, 3].foldl (collectorStep sampleSnapshot (fun _ => true)) WCertState.init).done = true := by
  decide
example :
    ([1, 2, 3].foldl (collectorStep sampleSnapshot (fun _ => true)) WCertState.init).accWeight = 2 := by
  decide

/-- The safe publish accepts a prefix-extending update and rejects a diverging one (output-prefix
    discipline). -/
example : safePublish ([1, 2] : List Nat) [1, 2, 3] = [1, 2, 3] := by decide
example : safePublish ([1, 2] : List Nat) [1, 3] = [1, 2] := by decide

/-- A number codec for extraction: a Wave or Hash is just a number atom here, and parsing reads it
    back. It is a left inverse, so extraction round-trips. -/
def numDec : Sexpr → Option Nat
  | .num n => some n
  | _ => none

#eval encodeFact (Wave := Nat) (Hash := Nat) Sexpr.num Sexpr.num (TrecFact.final 3 7)
-- (final 3 7)

/-- A `final` fact extracts to the atom `(final 3 7)` and parses straight back. -/
example :
    decodeFact numDec numDec (encodeFact Sexpr.num Sexpr.num (TrecFact.final 3 7))
      = some (TrecFact.final (Wave := Nat) (Hash := Nat) 3 7) := by decide

/-- The variable-length ordered-prefix fact also round-trips through MeTTaIL. -/
example :
    decodeFact numDec numDec (encodeFact Sexpr.num Sexpr.num (TrecFact.orderedPrefix [1, 2, 3]))
      = some (TrecFact.orderedPrefix (Wave := Nat) (Hash := Nat) [1, 2, 3]) := by decide

end CordialMiners.Tests
