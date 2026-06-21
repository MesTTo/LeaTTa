/-
Module: MeTTaILProofs.AxiomAudit
Layer: Proofs
Purpose: Build-visible axiom audit for the headline theorem surfaces. This module imports the operational
  and MeTTaIL proof results that the docs cite as checked, then runs `#print axioms` on the named
  declarations. The output should contain only Lean/Mathlib's standard classical axioms where the imported
  theorem uses Mathlib's classical infrastructure, and no project axiom or placeholder.
Imports: MettaHyperonFull.Operational.Properties, MeTTaILProofs.ConditionalCP, MeTTaILProofs.CPDemo,
  MeTTaILProofs.ConditionalCPRuntime, MeTTaILProofs.ACMatch, MeTTaILProofs.DistributiveLaw
Trusted boundary: none
Main exports: (audit output only)
Open obligations: keep this list aligned with the headline claims in the docs and proof-root comments.
-/
import MettaHyperonFull.Operational.Properties
import MeTTaILProofs.ConditionalCP
import MeTTaILProofs.CPDemo
import MeTTaILProofs.ConditionalCPRuntime
import MeTTaILProofs.ACMatch
import MeTTaILProofs.DistributiveLaw

#print axioms Metta.mem_equalityReductions
#print axioms Metta.smallStep?_kb_auditable
#print axioms Metta.resourceStep?_energy_nonincreasing

#print axioms MeTTaIL.subjectReduction_base
#print axioms MeTTaIL.matchPat_iff_instStruct

#print axioms MeTTaIL.CP.confluent_of_CPJ
#print axioms MeTTaIL.CP.c_confluent_of_joins
#print axioms MeTTaIL.CP.RewStep_confluent_on_emb
#print axioms MeTTaIL.CP.cong_RewStep_confluent_on_emb

#print axioms MeTTaIL.AC.matchPatAC_acRest_witness
#print axioms MeTTaIL.AC.matchPatAC_acRest_sound
#print axioms MeTTaIL.AC.ACRestFlatSplit
#print axioms MeTTaIL.AC.matchPatAC_acRest_complete_of_flat_split
#print axioms MeTTaIL.AC.matchPatAC_acRest_complete_of_fresh_split
#print axioms MeTTaIL.AC.matchPatAC_sound
#print axioms MeTTaIL.AC.oneStepAC'_sound
#print axioms MeTTaIL.AC.evalAC'_sound

#print axioms MeTTaIL.Beck.DistributiveLaw.composeMonad
