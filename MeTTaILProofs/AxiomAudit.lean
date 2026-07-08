-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.AxiomAudit
Layer: Proofs
Purpose: Build-visible axiom audit for the headline theorem surfaces. This module imports the operational
  and MeTTaIL proof results that the docs cite as checked, then runs `#print axioms` on the named
  declarations. The output should contain only Lean/Mathlib's standard classical axioms where the imported
  theorem uses Mathlib's classical infrastructure, and no project axiom or placeholder.
Imports: MettaHyperonFull.Operational.Properties, MeTTaIL.Semantics.Denotational,
  MeTTaIL.Semantics.Native, MeTTaIL.Semantics.NativeGrammar, MeTTaIL.Semantics.NativeTypes,
  MeTTaIL.Semantics.Hypercube, MeTTaIL.Semantics.CostRoundTrip, MeTTaIL.Semantics.KnottedUniverse,
  MeTTaIL.Semantics.RSet,
  MeTTaIL.Semantics.InteractingTrieMap, MeTTaIL.Semantics.Rho, MeTTaIL.Semantics.RhoKMachine,
  MeTTaIL.Semantics.RhoCompiler,
  MeTTaILProofs.ConditionalCP, MeTTaILProofs.CPDemo,
  MeTTaILProofs.ConditionalCPRuntime,
  MeTTaILProofs.ACMatch, MeTTaILProofs.DistributiveLaw
Trusted boundary: none
Main exports: (audit output only)
Open obligations: keep this list aligned with the headline claims in the docs and proof-root comments.
-/
import MettaHyperonFull.Operational.Properties
import MeTTaIL.Semantics.Denotational
import MeTTaIL.Semantics.Native
import MeTTaIL.Semantics.NativeGrammar
import MeTTaIL.Semantics.NativeTypes
import MeTTaIL.Semantics.Hypercube
import MeTTaIL.Semantics.CostRoundTrip
import MeTTaIL.Semantics.KnottedUniverse
import MeTTaIL.Semantics.RSet
import MeTTaIL.Semantics.InteractingTrieMap
import MeTTaIL.Semantics.Rho
import MeTTaIL.Semantics.RhoKMachine
import MeTTaIL.Semantics.RhoCompiler
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

#print axioms MeTTaIL.Denotational.bisimilar_isBisimulation
#print axioms MeTTaIL.Denotational.fullyAbstract_of_kernel
#print axioms MeTTaIL.Denotational.fullyAbstract_of_calibration
#print axioms MeTTaIL.Denotational.fullyAbstract_of_observation_calibration
#print axioms MeTTaIL.Denotational.fullyAbstract_of_bisimilarity_translation
#print axioms MeTTaIL.Denotational.congruence_of_bisimilarity_translation
#print axioms MeTTaIL.Denotational.FullyAbstractModel.eq_iff_bisimilar
#print axioms MeTTaIL.Denotational.FullyAbstractModel.pullback
#print axioms MeTTaIL.Denotational.StepTranslation.bisimilarityPreserving
#print axioms MeTTaIL.Denotational.StepTranslation.bisimilarityReflecting
#print axioms MeTTaIL.Denotational.NativeCarrier.source_bisimilar_of_native
#print axioms MeTTaIL.Denotational.NativeCarrier.native_bisimilar_of_source
#print axioms MeTTaIL.Denotational.NativeCarrier.toFullyAbstractModel
#print axioms MeTTaIL.Denotational.NativeCarrier.eq_iff_bisimilar
#print axioms MeTTaIL.Denotational.NativeCarrier.typeOf_eq_of_step
#print axioms MeTTaIL.Denotational.NativeSurface.SameNative.type_eq
#print axioms MeTTaIL.Denotational.NativeSurface.SameNative.denote_eq
#print axioms MeTTaIL.Denotational.NativeSurface.SameNative.bisimilar
#print axioms MeTTaIL.Denotational.NativeSurface.SameNative.denote_eq_iff_bisimilar
#print axioms MeTTaIL.Denotational.NativeEvidenceModel.evidence_eq_of_sameNative
#print axioms MeTTaIL.Denotational.NativeQueryModel.query_eq_of_sameNative
#print axioms MeTTaIL.Denotational.NativeQueryModel.evidence_eq_of_sameNative
#print axioms MeTTaIL.Denotational.NativeConstructorView.constructorPredicate_iff
#print axioms MeTTaIL.Denotational.NativeChecker.sound_of_reading
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.diamond_le_iff
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.searchSpec_iff_objectiveSpec
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.le_box_diamond
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.diamond_box_le
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.diamond_mono
#print axioms MeTTaIL.Denotational.NativeGaloisBridge.box_mono
#print axioms MeTTaIL.OSLF.Pred.future_box_galois
#print axioms MeTTaIL.OSLF.Pred.dia_pastBox_galois
#print axioms MeTTaIL.OSLF.Pred.le_box_future
#print axioms MeTTaIL.OSLF.Pred.future_box_le
#print axioms MeTTaIL.OSLF.Pred.le_pastBox_dia
#print axioms MeTTaIL.OSLF.Pred.dia_pastBox_le
#print axioms MeTTaIL.OSLF.NativeType.constructor_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.constructor_satisfies_self
#print axioms MeTTaIL.OSLF.NativeType.spatial_satisfies_sexp_iff
#print axioms MeTTaIL.OSLF.NativeType.arrow_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.dia_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.box_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.future_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.pastBox_satisfies_iff
#print axioms MeTTaIL.OSLF.NativeType.sortedBox_preserved
#print axioms MeTTaIL.OSLF.forwardGaloisBridge
#print axioms MeTTaIL.OSLF.possiblePastGaloisBridge
#print axioms MeTTaIL.Hypercube.Equation.admissible_iff
#print axioms MeTTaIL.Hypercube.centerMember_iff
#print axioms MeTTaIL.Hypercube.mem_equationalCenter_iff
#print axioms MeTTaIL.Hypercube.equationalCenter_sound
#print axioms MeTTaIL.Hypercube.equationalCenter_complete
#print axioms MeTTaIL.Hypercube.equationalCenter_nil
#print axioms MeTTaIL.AST.hypercubeContextVarsAt?_root
#print axioms MeTTaIL.AST.mem_hypercubeSubterms_root
#print axioms MeTTaIL.Hypercube.Slot.head_sortOp_eq
#print axioms MeTTaIL.Hypercube.Slot.sortExpr_eval_eq
#print axioms MeTTaIL.Hypercube.SlotConstraint.toEquation_inCenter_iff
#print axioms MeTTaIL.Hypercube.inEquationalCenter_slotConstraints_iff
#print axioms MeTTaIL.Hypercube.mem_constrainedCenter_iff
#print axioms MeTTaIL.Hypercube.SlotFamily.outputSlot_mem_slots
#print axioms MeTTaIL.Hypercube.SlotFamily.head_sortOp_eq
#print axioms MeTTaIL.Hypercube.SlotFamily.inputFootprint_within
#print axioms MeTTaIL.Hypercube.SlotFamily.outputFootprint_within
#print axioms MeTTaIL.Hypercube.SlotFamily.allFootprint_within
#print axioms MeTTaIL.Hypercube.ModalSite.slotFamily_slots_length
#print axioms MeTTaIL.Hypercube.ModalSite.outputSlot_mem_slotFamily
#print axioms MeTTaIL.Hypercube.SpatialHead.slotFamily_slots_length
#print axioms MeTTaIL.Hypercube.SpatialHead.outputSlot_mem_slotFamily
#print axioms MeTTaIL.Hypercube.TypeFamily.slotFamily_modal
#print axioms MeTTaIL.Hypercube.TypeFamily.slotFamily_spatial
#print axioms MeTTaIL.Hypercube.RuleScheme.outputSlot_mem_slotFamily
#print axioms MeTTaIL.Hypercube.RuleScheme.footprintSlots_subset_slots
#print axioms MeTTaIL.Hypercube.RuleScheme.footprints_within
#print axioms MeTTaIL.Hypercube.ModalSite.ruleKinds_length
#print axioms MeTTaIL.Hypercube.ModalSite.ruleSchemes_length
#print axioms MeTTaIL.Hypercube.ModalSite.ruleSchemes_compatible
#print axioms MeTTaIL.Hypercube.SpatialHead.ruleKinds_length
#print axioms MeTTaIL.Hypercube.SpatialHead.ruleSchemes_length
#print axioms MeTTaIL.Hypercube.SpatialHead.ruleSchemes_compatible
#print axioms MeTTaIL.Denotational.PathRSpace.prefix_trans
#print axioms MeTTaIL.Denotational.PathRSpace.comparable_iff_nonempty_subspaceBranch
#print axioms MeTTaIL.Denotational.PathRSpace.SubspaceSystem.branch_of_step
#print axioms MeTTaIL.Denotational.Bisimilar.trans
#print axioms MeTTaIL.Denotational.Costed.costedStep_forget
#print axioms MeTTaIL.Denotational.Costed.Trace.to_reflTransGen
#print axioms MeTTaIL.Denotational.Costed.costDeadlocked_iff_forget_deadlocked
#print axioms MeTTaIL.Denotational.Costed.Trace.to_stepCount
#print axioms MeTTaIL.Denotational.Costed.Trace.to_stepCount_of_unitTokenCosted
#print axioms MeTTaIL.Denotational.Costed.ContinuedCostSystem.starved_costDeadlocked
#print axioms MeTTaIL.Denotational.Costed.ContinuedCostSystem.starved_deadlocked
#print axioms MeTTaIL.Denotational.Costed.ContinuedCostSystem.wrapped_trace_preserved
#print axioms MeTTaIL.Denotational.Costed.CostRoundTrip.image_subset_fixed
#print axioms MeTTaIL.Denotational.Costed.CostRoundTrip.fixed_subset_image
#print axioms MeTTaIL.Denotational.Costed.CostRoundTrip.image_iff_fixed
#print axioms MeTTaIL.Denotational.eval_rewrite_trace

#print axioms MeTTaIL.KnottedUniverse.Colour.swap_swap
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverse.dropRed_quoteRed
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverse.quoteRed_dropRed
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverse.dropBlack_quoteBlack
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverse.quoteBlack_dropBlack
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverseHom.id
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverseHom.comp
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverseHom.ext
#print axioms MeTTaIL.KnottedUniverse.ReflectiveUniverse.category
#print axioms MeTTaIL.KnottedUniverse.CoalgebraHom.id
#print axioms MeTTaIL.KnottedUniverse.CoalgebraHom.comp
#print axioms MeTTaIL.KnottedUniverse.CoalgebraHom.ext
#print axioms MeTTaIL.KnottedUniverse.Coalgebra.category
#print axioms MeTTaIL.KnottedUniverse.FinalCoalgebra.lift_commutes
#print axioms MeTTaIL.KnottedUniverse.FinalCoalgebra.finalHom
#print axioms MeTTaIL.KnottedUniverse.FinalCoalgebra.finalHom_unique
#print axioms MeTTaIL.KnottedUniverse.FinalCoalgebra.isTerminal
#print axioms MeTTaIL.KnottedUniverse.FinalCoalgebra.identity
#print axioms MeTTaIL.KnottedUniverse.FinalBehaviourModel.toFullyAbstractModel
#print axioms MeTTaIL.KnottedUniverse.FinalBehaviourModel.eq_iff_bisimilar
#print axioms MeTTaIL.KnottedUniverse.FinalBehaviourModel.fullyAbstractFor
#print axioms MeTTaIL.KnottedUniverse.FinalBehaviourModel.fullyAbstractForObservations

#print axioms MeTTaIL.RSetModel.twoColourAutomaton_no_self_loop
#print axioms MeTTaIL.RSetModel.RElem.quoteAtom_dropAtom
#print axioms MeTTaIL.RSetModel.RSet.renameAtoms_eq_of_forall_mem_atomsOf
#print axioms MeTTaIL.RSetModel.RSet.renameAtoms_eq_of_supports
#print axioms MeTTaIL.RSetModel.RSet.renameAtoms_id
#print axioms MeTTaIL.RSetModel.RSet.toExt_eq_of_extEq
#print axioms MeTTaIL.RSetModel.RSet.mem_union_iff
#print axioms MeTTaIL.RSetModel.RSet.extEq_union_congr
#print axioms MeTTaIL.RSetModel.RSet.extEq_empty_union
#print axioms MeTTaIL.RSetModel.RSet.extEq_union_empty
#print axioms MeTTaIL.RSetModel.RSet.extEq_union_idem
#print axioms MeTTaIL.RSetModel.RSet.extEq_union_comm
#print axioms MeTTaIL.RSetModel.RSet.extEq_union_assoc
#print axioms MeTTaIL.RSetModel.blackToRedSet_redToBlackSet
#print axioms MeTTaIL.RSetModel.redToBlackSet_blackToRedSet
#print axioms MeTTaIL.RSetModel.reflective_dropRed_quoteRed
#print axioms MeTTaIL.RSetModel.reflective_quoteRed_dropRed
#print axioms MeTTaIL.RSetModel.reflective_dropBlack_quoteBlack
#print axioms MeTTaIL.RSetModel.reflective_quoteBlack_dropBlack
#print axioms MeTTaIL.RSetModel.reflective_redBlackSetSwap
#print axioms MeTTaIL.RSetModel.reflective_blackRedSetSwap
#print axioms MeTTaIL.RSetModel.reflective_redBlackAtomSwap
#print axioms MeTTaIL.RSetModel.reflective_blackRedAtomSwap

#print axioms MeTTaIL.InteractingTrieMap.RITM.ofStep_toStep
#print axioms MeTTaIL.InteractingTrieMap.RITM.toStep_ofStep
#print axioms MeTTaIL.InteractingTrieMap.RITM.stepEquiv
#print axioms MeTTaIL.InteractingTrieMap.PackedBinding.root_prefix_address
#print axioms MeTTaIL.InteractingTrieMap.PackedBinding.root_comparable_address
#print axioms MeTTaIL.InteractingTrieMap.Colour.swap_swap

#print axioms MeTTaIL.Rho.step_to_mod
#print axioms MeTTaIL.Rho.RSpace.fits_one
#print axioms MeTTaIL.Rho.RSpace.comm_to_step_one
#print axioms MeTTaIL.Rho.listener_step
#print axioms MeTTaIL.Rho.payloadForwarder_emits
#print axioms MeTTaIL.Rho.KMachine.readyPair_of_output_records_input
#print axioms MeTTaIL.Rho.KMachine.readyPair_of_input_records_output
#print axioms MeTTaIL.Rho.KMachine.creation_to_struct
#print axioms MeTTaIL.Rho.KMachine.step_to_rho
#print axioms MeTTaIL.Rho.KMachine.ordinaryReceive_to_rho
#print axioms MeTTaIL.Rho.KMachine.persistentOutput_to_rho
#print axioms MeTTaIL.Rho.KMachine.persistentReceive_to_rho
#print axioms MeTTaIL.Rho.KMachine.persistentBoth_to_rho
#print axioms MeTTaIL.Rho.Compiler.contractumForwarder_emits
#print axioms MeTTaIL.Rho.Compiler.contractum_kstep
#print axioms MeTTaIL.Rho.Compiler.contractumRun_struct_kSource
#print axioms MeTTaIL.Rho.Compiler.contractum_kstep_to_rho
#print axioms MeTTaIL.Rho.Compiler.contractumRun_kstep_to_rho
#print axioms MeTTaIL.Rho.Compiler.applyBaseRewrite_reduces_and_emits
#print axioms MeTTaIL.Rho.Compiler.applyBaseRewrite_reduces_emits_and_reifies_kstep
#print axioms MeTTaIL.Rho.drop_termLocation
#print axioms MeTTaIL.Rho.receivedVar_drops
