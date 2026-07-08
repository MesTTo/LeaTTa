-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Distributed.AxiomAudit
Layer: Distributed
Purpose: Build-visible axiom audit for the active DAS theorem surface. Fair delivery and ordered
  replay are theorem parameters in `DAS.lean`, not Lean axioms, so the audit should not report
  project-level distributed-system axioms.
Imports: MettaHyperonFull.Distributed.DAS
Trusted boundary: none
Main exports: audit output only
Open obligations: keep this list aligned with the mechanization ledger.
-/
import MettaHyperonFull.Distributed.DAS

#print axioms Metta.Distributed.vcLeRefl
#print axioms Metta.Distributed.vcLeTrans
#print axioms Metta.Distributed.vcLeAntisym
#print axioms Metta.Distributed.vcGet_vcMax
#print axioms Metta.Distributed.vcLeMaxLeft
#print axioms Metta.Distributed.vcLeMaxRight
#print axioms Metta.Distributed.vcMaxLub
#print axioms Metta.Distributed.readOwnWrites
#print axioms Metta.Distributed.eventualDelivery
#print axioms Metta.Distributed.barrierExtensionViaEventualDelivery
#print axioms Metta.Distributed.causalConsistency
#print axioms Metta.Distributed.midFlightDivergence
#print axioms Metta.Distributed.dasConvergence
#print axioms Metta.Distributed.sigmaConvergence
#print axioms Metta.Distributed.convergedMatchingBehavior
