/-
Module: MettaHyperonFull.Proofs.MultipleSignatureSelection
Layer: Proofs
Purpose: Pin the ordered multi-signature evaluator repair and the legacy last-write-wins defect.
Imports: MettaHyperonFull.Proofs.TypeSoundness
Trusted boundary: none
Main exports: legacy_signature_index_keeps_only_last, ordered_selection_uses_first_applicable,
  ordered_selection_skips_failed_candidate, ordered_selection_retains_all_errors,
  selected_signature_owns_argument_mask, mettaEval_uses_first_applicable_signature
Open obligations: none
-/
import MettaHyperonFull.Proofs.TypeSoundness
import MettaHyperonFull.Proofs.Substitution
import Std.Data.HashMap.Lemmas

/-!
# Ordered multiple-signature selection

The evaluator and `getTypes` now share the same source-ordered declaration list.  These theorems
retain the old overwrite as a negative canary and pin first-applicable selection, complete failure
retention, tuple eligibility, selected-signature masks, and the repaired observable result.
-/

namespace Metta
open Metta.Minimal

private def arrowA : Atom :=
  .expr [.sym "->", .sym "A", .sym "RA"]

private def arrowB : Atom :=
  .expr [.sym "->", .sym "B", .sym "RB"]

private def applicationA : Atom :=
  .expr [.sym "f", .sym "a"]

private def multiSignatureAtoms : List Atom := [
  .expr [.sym ":", .sym "f", arrowA],
  .expr [.sym ":", .sym "f", arrowB],
  .expr [.sym ":", .sym "a", .sym "A"]]

private def multiSignatureEnv : MinEnv :=
  MinEnv.ofAtomsGT multiSignatureAtoms []

private theorem typePrep_empty_symbol (name : String) :
    typePrep World.empty (.sym name) = .sym name := by
  simp [typePrep, subTokens.eq_1, wrapStates.eq_3, World.empty]

open Std in
/-- Isolated reproduction of the removed cache: every new arrow declaration overwrites its
predecessor.  It remains only so the original failure mechanism cannot be reintroduced unnoticed. -/
def legacySignatureIndex (atoms : List Atom) : HashMap String (List Atom) :=
  atoms.foldl (fun index atom => match atom with
    | .expr [.sym ":", .sym operator, .expr (.sym "->" :: signature)] =>
        index.insert operator signature
    | _ => index) HashMap.emptyWithCapacity

/-- Negative canary: the removed cache loses the earlier declaration. -/
theorem legacy_signature_index_keeps_only_last :
    (legacySignatureIndex multiSignatureAtoms).get? "f" =
      some [.sym "B", .sym "RB"] := by
  simp [legacySignatureIndex, multiSignatureAtoms, arrowA, arrowB]

/-- The surviving declaration index retains both signatures in source order. -/
theorem getTypes_keeps_both_signatures :
    getTypes multiSignatureEnv (.sym "f") = [arrowA, arrowB] := by
  rw [getTypes.eq_8]
  simp [multiSignatureEnv, multiSignatureAtoms, MinEnv.ofAtomsGT,
    arrowA, arrowB, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity]

private theorem multiSignature_a_type :
    getTypes multiSignatureEnv (.sym "a") = [.sym "A"] := by
  rw [getTypes.eq_8]
  simp [multiSignatureEnv, multiSignatureAtoms, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem multiSignature_check_A_detailed :
    typeCheckArgsDetailedOutcome multiSignatureEnv World.empty [.sym "A"] 0 [] [.sym "a"] =
      .success [] [] := by
  have hmatch : matchType [] (.sym "A") (.sym "A") = some [] := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, multiSignature_a_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem multiSignature_check_A :
    typeCheckArgsOutcome multiSignatureEnv World.empty [.sym "A"] 0 [] [.sym "a"] =
      .success [] := by
  rw [typeCheckArgsOutcome, multiSignature_check_A_detailed]

private theorem multiSignature_selection :
    selectFunctionType multiSignatureEnv World.empty (.sym "f") [.sym "a"] =
      .selected ⟨arrowA, [.sym "A"], .sym "RA", []⟩ := by
  rw [selectFunctionType, typePrep_empty_symbol, getTypes_keeps_both_signatures]
  simp [scanFunctionTypeCandidates, arrowA, multiSignature_check_A_detailed]

/-- The first candidate is applicable, so the scan stops without consulting the later one. -/
theorem ordered_selection_uses_first_applicable :
    ∃ selected, selectFunctionType multiSignatureEnv World.empty (.sym "f") [.sym "a"] =
        .selected selected ∧ selected.functionType = arrowA := by
  refine ⟨⟨arrowA, [.sym "A"], .sym "RA", []⟩, ?_, rfl⟩
  exact multiSignature_selection

private def reverseSignatureEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", arrowB],
    .expr [.sym ":", .sym "f", arrowA],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private theorem reverse_f_types :
    getTypes reverseSignatureEnv (.sym "f") = [arrowB, arrowA] := by
  rw [getTypes.eq_8]
  simp [reverseSignatureEnv, MinEnv.ofAtomsGT, arrowA, arrowB,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem reverse_a_type :
    getTypes reverseSignatureEnv (.sym "a") = [.sym "A"] := by
  rw [getTypes.eq_8]
  simp [reverseSignatureEnv, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem reverse_check_B_detailed :
    typeCheckArgsDetailedOutcome reverseSignatureEnv World.empty [.sym "B"] 0 [] [.sym "a"] =
      .failure { position := 1, expected := .sym "B", actual := .sym "A" } [] := by
  have hmatch : matchType [] (.sym "B") (.sym "A") = none := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, reverse_a_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem reverse_check_B :
    typeCheckArgsOutcome reverseSignatureEnv World.empty [.sym "B"] 0 [] [.sym "a"] =
      .failure 1 (.sym "B") (.sym "A") := by
  rw [typeCheckArgsOutcome, reverse_check_B_detailed]

private theorem reverse_check_A_detailed :
    typeCheckArgsDetailedOutcome reverseSignatureEnv World.empty [.sym "A"] 0 [] [.sym "a"] =
      .success [] [] := by
  have hmatch : matchType [] (.sym "A") (.sym "A") = some [] := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, reverse_a_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem reverse_check_A :
    typeCheckArgsOutcome reverseSignatureEnv World.empty [.sym "A"] 0 [] [.sym "a"] =
      .success [] := by
  rw [typeCheckArgsOutcome, reverse_check_A_detailed]

/-- An inapplicable first declaration is skipped and the later applicable declaration wins. -/
theorem ordered_selection_skips_failed_candidate :
    ∃ selected, selectFunctionType reverseSignatureEnv World.empty (.sym "f") [.sym "a"] =
        .selected selected ∧ selected.functionType = arrowA := by
  refine ⟨⟨arrowA, [.sym "A"], .sym "RA", []⟩, ?_, rfl⟩
  rw [selectFunctionType, typePrep_empty_symbol, reverse_f_types]
  simp [scanFunctionTypeCandidates, arrowA, arrowB,
    reverse_check_B_detailed, reverse_check_A_detailed,
    FunctionTypeScanOutcome.prependErrors]

private def allFailedEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", arrowA],
    .expr [.sym ":", .sym "f", arrowB],
    .expr [.sym ":", .sym "c", .sym "C"]] []

private theorem allFailed_f_types :
    getTypes allFailedEnv (.sym "f") = [arrowA, arrowB] := by
  rw [getTypes.eq_8]
  simp [allFailedEnv, MinEnv.ofAtomsGT, arrowA, arrowB,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem allFailed_c_type :
    getTypes allFailedEnv (.sym "c") = [.sym "C"] := by
  rw [getTypes.eq_8]
  simp [allFailedEnv, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem allFailed_check_A_detailed :
    typeCheckArgsDetailedOutcome allFailedEnv World.empty [.sym "A"] 0 [] [.sym "c"] =
      .failure { position := 1, expected := .sym "A", actual := .sym "C" } [] := by
  have hmatch : matchType [] (.sym "A") (.sym "C") = none := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, allFailed_c_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem allFailed_check_A :
    typeCheckArgsOutcome allFailedEnv World.empty [.sym "A"] 0 [] [.sym "c"] =
      .failure 1 (.sym "A") (.sym "C") := by
  rw [typeCheckArgsOutcome, allFailed_check_A_detailed]

private theorem allFailed_check_B_detailed :
    typeCheckArgsDetailedOutcome allFailedEnv World.empty [.sym "B"] 0 [] [.sym "c"] =
      .failure { position := 1, expected := .sym "B", actual := .sym "C" } [] := by
  have hmatch : matchType [] (.sym "B") (.sym "C") = none := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, allFailed_c_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem allFailed_check_B :
    typeCheckArgsOutcome allFailedEnv World.empty [.sym "B"] 0 [] [.sym "c"] =
      .failure 1 (.sym "B") (.sym "C") := by
  rw [typeCheckArgsOutcome, allFailed_check_B_detailed]

/-- When no function candidate applies, every error is retained in declaration order. -/
theorem ordered_selection_retains_all_errors :
    selectFunctionType allFailedEnv World.empty (.sym "f") [.sym "c"] =
      .exhausted [
        .badArgument 1 (.sym "A") (.sym "C"),
        .badArgument 1 (.sym "B") (.sym "C")] false := by
  rw [selectFunctionType, typePrep_empty_symbol, allFailed_f_types]
  simp [scanFunctionTypeCandidates, arrowA, arrowB,
    allFailed_check_A_detailed, allFailed_check_B_detailed,
    FunctionTypeScanOutcome.prependErrors,
    TypeCheckArgsError.toFunctionTypeError]

private def atomMaskEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "hold", .expr [.sym "->", .sym "Atom", .sym "Atom"]],
    .expr [.sym ":", .sym "hold", .expr [.sym "->", .sym "A", .sym "Atom"]],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private theorem atomMask_hold_types :
    getTypes atomMaskEnv (.sym "hold") =
      [.expr [.sym "->", .sym "Atom", .sym "Atom"],
       .expr [.sym "->", .sym "A", .sym "Atom"]] := by
  rw [getTypes.eq_8]
  simp [atomMaskEnv, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem atomMask_a_type :
    getTypes atomMaskEnv (.sym "a") = [.sym "A"] := by
  rw [getTypes.eq_8]
  simp [atomMaskEnv, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem atomMask_check_detailed :
    typeCheckArgsDetailedOutcome atomMaskEnv World.empty [.sym "Atom"] 0 [] [.sym "a"] =
      .success [] [] := by
  have hmatch : matchType [] (.sym "Atom") (.sym "A") = some [] := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, atomMask_a_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem atomMask_check :
    typeCheckArgsOutcome atomMaskEnv World.empty [.sym "Atom"] 0 [] [.sym "a"] =
      .success [] := by
  rw [typeCheckArgsOutcome, atomMask_check_detailed]

/-- The selected signature, not a separate cache entry, determines quoted-argument behavior. -/
theorem selected_signature_owns_argument_mask :
    ∃ selected, selectFunctionType atomMaskEnv World.empty (.sym "hold") [.sym "a"] =
        .selected selected ∧ argMask selected 1 = [false] := by
  refine ⟨⟨.expr [.sym "->", .sym "Atom", .sym "Atom"],
    [.sym "Atom"], .sym "Atom", []⟩, ?_, ?_⟩
  · rw [selectFunctionType, typePrep_empty_symbol, atomMask_hold_types]
    simp [scanFunctionTypeCandidates, atomMask_check_detailed]
  · have hquoted : ((.sym "Atom" : Atom) != .sym "Atom") = false := by rfl
    simp [argMask, instantiate_nil, hquoted]

private def mixedTupleEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", .sym "Data"],
    .expr [.sym ":", .sym "f", arrowB],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private theorem mixed_f_types :
    getTypes mixedTupleEnv (.sym "f") = [.sym "Data", arrowB] := by
  rw [getTypes.eq_8]
  simp [mixedTupleEnv, MinEnv.ofAtomsGT, arrowB,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem mixed_a_type :
    getTypes mixedTupleEnv (.sym "a") = [.sym "A"] := by
  rw [getTypes.eq_8]
  simp [mixedTupleEnv, MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem mixed_check_B_detailed :
    typeCheckArgsDetailedOutcome mixedTupleEnv World.empty [.sym "B"] 0 [] [.sym "a"] =
      .failure { position := 1, expected := .sym "B", actual := .sym "A" } [] := by
  have hmatch : matchType [] (.sym "B") (.sym "A") = none := by rfl
  simp [typeCheckArgsDetailedOutcome, typeCheckArgsDetailedOutcomeScoped,
    applicationTypeInferenceScope, scanActualTypes,
    typePrep_empty_symbol, mixed_a_type,
    freshenTypeCandidate, renameAllVars, instantiate_nil, hmatch]

private theorem mixed_check_B :
    typeCheckArgsOutcome mixedTupleEnv World.empty [.sym "B"] 0 [] [.sym "a"] =
      .failure 1 (.sym "B") (.sym "A") := by
  rw [typeCheckArgsOutcome, mixed_check_B_detailed]

/-- A non-function candidate enables tuple interpretation only after every function candidate
fails; its function error is retained alongside that eligibility. -/
theorem exhausted_scan_retains_tuple_eligibility :
    selectFunctionType mixedTupleEnv World.empty (.sym "f") [.sym "a"] =
      .exhausted [.badArgument 1 (.sym "B") (.sym "A")] true := by
  rw [selectFunctionType, typePrep_empty_symbol, mixed_f_types]
  simp [scanFunctionTypeCandidates, arrowB, mixed_check_B_detailed,
    FunctionTypeScanOutcome.prependErrors,
    TypeCheckArgsError.toFunctionTypeError,
    FunctionTypeScanOutcome.markTupleEligible]

private theorem multiSignature_interpret_a :
    interpretFuel multiSignatureEnv 1 St.init
      [{ stack := atomToStack (.expr [.sym "eval", .sym "a"]) [], bnd := [] }] [] =
      ([(notReducibleA, [])], St.init) := by
  have hNotEmpty : (notReducibleA != emptyA) = true := by rfl
  simp [interpretFuel.eq_3, interpretFuel.eq_1, interpretStack1.eq_1,
    atomToStack, evalOp, queryOp, candidatesW, MinEnv.candidates, extractRules,
    instantiate_nil, multiSignatureEnv, multiSignatureAtoms, MinEnv.ofAtomsGT,
    St.init, World.empty, isEmbeddedOp, isVariableHeaded, headKey, finItem,
    isFinal, finalPair, Std.HashMap.getD_emptyWithCapacity, hNotEmpty]

private theorem multiSignature_eval_a :
    mettaEval multiSignatureEnv 1 St.init [] (.sym "a") =
      ([(.sym "a", [])], St.init) := by
  have hNotEmpty : ((.sym "a" : Atom) == emptyA) = false := rfl
  have hNotError : (.sym "a" : Atom).isError = false := rfl
  simp [mettaEval, instantiate_nil, hNotEmpty, hNotError,
    prioritizeSemanticResults]

private theorem multiSignature_eval_a_expected :
    mettaEvalExpected multiSignatureEnv 1 St.init [] (.sym "a") (.sym "A") =
      ([(.sym "a", [])], St.init) := by
  have hExpected : ((.sym "A" : Atom) == .sym "%Undefined%") = false := rfl
  have hMatch : matchType [] (.sym "A") (.sym "A") = some [] := by rfl
  have hCast :
      mettaTypeCast multiSignatureEnv St.init.world [] (.sym "a") (.sym "A") =
        .inr [] := by
    rw [mettaTypeCast]
    simp only [St.init]
    rw [typePrep_empty_symbol, multiSignature_a_type]
    rw [show freshenArgumentTypes
      (typeCastInferenceAvoid multiSignatureEnv (.sym "a") (.sym "a")
        (.sym "A") [] [.sym "A"]) 0 [.sym "A"] = [.sym "A"] by
      simp [freshenArgumentTypes, freshenTypeCandidate, renameAllVars]]
    simp only [matchExpectedType]
    rw [hMatch]
  simp [mettaEvalExpected, hExpected, instantiate_nil, hCast,
    prioritizeSemanticResults]

private theorem multiSignature_reduce_application :
    interpretFuel multiSignatureEnv 2 St.init
      [{ stack := atomToStack (.expr [.sym "eval", applicationA]) [], bnd := [] }] [] =
      ([(notReducibleA, [])], St.init) := by
  have hNotEmpty : (notReducibleA != emptyA) = true := by rfl
  simp [interpretFuel.eq_3, interpretFuel.eq_1, interpretStack1.eq_1,
    atomToStack, evalOp, queryOp, candidatesW, MinEnv.candidates, extractRules,
    instantiate_nil, applicationA, multiSignatureEnv, multiSignatureAtoms,
    MinEnv.ofAtomsGT, St.init, World.empty, isEmbeddedOp, isVariableHeaded,
    headKey, finItem, isFinal, finalPair, callGrounded,
    GroundingTable.lookup, Std.HashMap.getD_emptyWithCapacity, hNotEmpty]

/-- Observable repair canary: the earlier applicable declaration is no longer masked by the later
incompatible declaration. -/
theorem mettaEval_uses_first_applicable_signature :
    (mettaEval multiSignatureEnv 2 St.init [] applicationA).1 =
      [(applicationA, [])] := by
  rw [mettaEval.eq_2, instantiate_nil]
  simp only [applicationA]
  have hSelection :
      selectFunctionType multiSignatureEnv St.init.world (.sym "f") [.sym "a"] =
        .selected ⟨arrowA, [.sym "A"], .sym "RA", []⟩ := by
    simpa [St.init] using multiSignature_selection
  rw [hSelection]
  simp only
  have hPolicies :
      argumentEvaluationPolicies
        ⟨arrowA, [.sym "A"], .sym "RA", []⟩ 1 =
        [(true, .sym "A")] := by
    have hAtom : ((.sym "A" : Atom) != .sym "Atom") = true := by rfl
    have hVariable : ((.sym "A" : Atom) != .sym "Variable") = true := by rfl
    have hExpression : ((.sym "A" : Atom) != .sym "Expression") = true := by rfl
    simp [argumentEvaluationPolicies, instantiate_nil,
      hAtom, hVariable, hExpression]
  have hReturn : returnsAtom ⟨arrowA, [.sym "A"], .sym "RA", []⟩ = false := by
    have hRA : ((.sym "RA" : Atom) == .sym "Atom") = false := by rfl
    simp [returnsAtom, instantiate_nil, hRA]
  change
    (prioritizeSemanticResults (evaluateExpectedApplication
      (fun nextSt nextBindings nextAtom nextExpected =>
        mettaEvalExpected multiSignatureEnv 1 nextSt nextBindings nextAtom
          nextExpected)
      (fun nextSt application =>
        interpretFuel multiSignatureEnv 2 nextSt
          [{ stack := atomToStack (.expr [.sym "eval", application]) [], bnd := [] }] [])
      St.init "f" [.sym "a"]
      ⟨arrowA, [.sym "A"], .sym "RA", []⟩)).1 =
        [(.expr [.sym "f", .sym "a"], [])]
  have hReduce :
      interpretFuel multiSignatureEnv 2 St.init
        [{ stack := atomToStack (.expr [.sym "eval", .expr [.sym "f", .sym "a"]]) [],
           bnd := [] }] [] = ([(notReducibleA, [])], St.init) := by
    simpa [applicationA] using multiSignature_reduce_application
  have hNotError : (.sym "a" : Atom).isError = false := by rfl
  have hSame : ((.sym "a" : Atom) != .sym "a") = false := by rfl
  have hNotReducibleSelf : (notReducibleA == notReducibleA) = true := by rfl
  have hMerge : Bindings.merge [] [] = [[]] := by rfl
  have hVars : (.sym "a" : Atom).vars = [] := by simp [Atom.vars]
  have hRestrict : restrictBnd [] [] = [] := by rfl
  have hApplicationNotError :
      (Atom.expr [Atom.sym "f", Atom.sym "a"]).isError = false := rfl
  simp [evaluateExpectedApplication, evaluateExpectedApplicationFrom,
    hPolicies, hReturn,
    multiSignature_eval_a_expected, hReduce, hNotError, hSame,
    hNotReducibleSelf, hMerge, hVars, hRestrict,
    hApplicationNotError, prioritizeSemanticResults]

/-! ## Published evaluation-boundary canaries -/

/-- A semantic success suppresses a latent error while retaining the state
reached after exploring both alternatives.  This is the list-level boundary
used by the mixed tuple/function lane above. -/
theorem prioritizeSemanticResults_success_then_error
    (success error : Atom × Bindings) (st : St)
    (successNotError : success.1.isError = false)
    (errorIsError : error.1.isError = true) :
    prioritizeSemanticResults ([success, error], st) = ([success], st) := by
  simp [prioritizeSemanticResults, successNotError, errorIsError]

/-- Bare symbols are data at the published `metta` boundary.  In particular,
an equality rule whose left-hand side is the same symbol is not consulted
until the symbol occurs in an executable expression. -/
theorem mettaEval_symbol_passthrough (env : MinEnv) (fuel : Nat) (st : St)
    (bindings : Bindings) (name : String) :
    mettaEval env (fuel + 1) st bindings (.sym name) =
      ([(.sym name, bindings)], st) := by
  rw [mettaEval.eq_2,
    instantiate_of_closed bindings (.sym name) (by simp [Atom.vars])]
  simp [prioritizeSemanticResults]

/-- The empty expression is a successful value, not an instruction to invoke
the equation reducer. -/
theorem mettaEval_empty_passthrough (env : MinEnv) (fuel : Nat) (st : St)
    (bindings : Bindings) :
    mettaEval env (fuel + 1) st bindings emptyA =
      ([(emptyA, bindings)], st) := by
  have emptySelf : (emptyA == emptyA) = true := by rfl
  rw [mettaEval.eq_2,
    instantiate_of_closed bindings emptyA (by simp [emptyA, Atom.vars])]
  simp [emptySelf]

/-- Syntactic error expressions are already final at the public evaluator
boundary.  The result atom is instantiated once, but is never reduced as an
ordinary application. -/
theorem mettaEval_error_passthrough (env : MinEnv) (fuel : Nat) (st : St)
    (bindings : Bindings) (sourceName messageName : String) :
    mettaEval env (fuel + 1) st bindings
        (.expr [.sym "Error", .sym sourceName, .sym messageName]) =
      ([(.expr [.sym "Error", .sym sourceName, .sym messageName], bindings)],
        st) := by
  have closed :
      (.expr [.sym "Error", .sym sourceName, .sym messageName] : Atom).vars = [] := by
    simp [Atom.vars]
  rw [mettaEval.eq_2, instantiate_of_closed bindings _ closed]
  simp [Atom.isError]

end Metta
