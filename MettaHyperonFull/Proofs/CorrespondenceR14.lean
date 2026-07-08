-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.CorrespondenceR14
Layer: Proofs
Purpose: R.1-R.4 presentation of the existing QUERY correspondence proof. The theorem content lives
  in Correspondence.lean; this file packages it into the four public obligations: initial agreement,
  step matching, observation compatibility, and termination preservation.
Imports: MettaHyperonFull.Proofs.Correspondence
Trusted boundary: none
Main exports: QueryCorrespondenceR14, queryCorrespondenceR14
Open obligations: extend this presentation when the full evaluator, beyond the QUERY reduct-set core,
  receives a theorem-level observation relation.
-/
import MettaHyperonFull.Proofs.Correspondence

namespace Metta
open Metta.Minimal

/-- Four-obligation presentation of the QUERY correspondence. -/
structure QueryCorrespondenceR14 (atoms : List Atom) (gt : GroundingTable) : Prop where
  initialAgreement : forall a : Atom, a = a
  stepMatching : forall {a a'}, KernelStep atoms gt a a' <-> MopsStep atoms a a'
  observationCompatibility : forall {a k x}, headKey a = some k ->
    (x ∈ firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates a) a <->
      x ∈ equalityReductions ⟨atoms⟩ a)
  terminationPreservation : forall {a k}, headKey a = some k ->
    (firedReducts ((MinEnv.ofAtomsGT atoms gt).candidates a) a = [] <->
      equalityReductions ⟨atoms⟩ a = [])

/-- The existing QUERY correspondence satisfies the R.1-R.4 presentation. -/
theorem queryCorrespondenceR14 (atoms : List Atom) (gt : GroundingTable) :
    QueryCorrespondenceR14 atoms gt := by
  exact {
    initialAgreement := fun _ => rfl
    stepMatching := fun {a} {a'} => kernelStep_iff_mopsStep (atoms := atoms) (gt := gt)
      (a := a) (a' := a')
    observationCompatibility := fun {a} {k} {x} hk =>
      kernel_query_eq_mops_query (atoms := atoms) (gt := gt) (toEval := a) (k := k) hk x
    terminationPreservation := fun {a} {k} hk =>
      kernel_irreducible_iff_mops_insensitive (atoms := atoms) (gt := gt) (toEval := a) (k := k) hk
  }

end Metta
