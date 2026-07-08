-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: CordialMiners.AxiomAudit
Layer: Proofs
Purpose: Build-visible axiom audit for the public Cordial Miners proof surface.
Imports: CordialMiners.Proofs.EndToEndSafety, CordialMiners.Runtime.AxiomAudit
Trusted boundary: none
Main exports: (audit output only)
Open obligations: keep this list aligned with the README and book theorem registry.
-/
import CordialMiners.Proofs.EndToEndSafety
import CordialMiners.Runtime.AxiomAudit

#print axioms CordialMiners.EndToEndSafety
#print axioms CordialMiners.EndToEndAssumptions
#print axioms CordialMiners.threshold_certificates_agree
#print axioms CordialMiners.end_to_end_safety_of_output_monotone
#print axioms CordialMiners.topoSort_valid
#print axioms CordialMiners.end_to_end_safety_of_anchor_prefix_monotone
#print axioms CordialMiners.end_to_end_safety_of_finalized_count_monotone
#print axioms CordialMiners.end_to_end_safety_of_finality_permanence
