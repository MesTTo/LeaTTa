-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.TypeSoundness
Layer: Proofs
Purpose: The gradual type system is permissive, total, and reports errors faithfully. Undeclared
  operators, extra arguments, and the wildcards %Undefined%/Atom are never rejected, getTypes assigns
  every atom at least one type, a reported BadArgType always names a real actual type, and the runtime
  invents no type errors. Preservation for the grounded numeric core: arithmetic is closed on Number,
  comparison and == yield Bool or faithfully propagate an error.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: typeMismatch_undeclared, matchType_undefined_left, matchType_undefined_right,
  matchType_atom_left, matchType_atom_right, typeCheckArgs_no_param, mettaEval_badArgType,
  getTypes_ne_nil, getTypes_unique_modulo_permutation, TypeCandidateFresheningRel,
  typeCheckArgs_act_real, numBin_isNumber,
  numCmp_isBool, eqAtom_isBoolOrError
Open obligations: none. Subject reduction over user-defined =-rewriting is proved in Preservation.lean.
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: gradual type system, permissiveness and faithful error reporting

MeTTa's type system (`Minimal/Interpreter.lean`: `getTypes`, `matchType`, `typeCheckArgs`,
`selectFunctionType`) is *gradual*: a declared arrow signature `(: op (-> T₁ … Tₙ R))` causes argument
type-checking, an undeclared operator is left unchecked, and the special types `%Undefined%` and
`Atom` are compatible with anything. A genuine mismatch surfaces at runtime as
`(Error (op …) (BadArgType pos expected actual))` (Hyperon's `BadArgType`).

For on-chain use, two properties matter: a well-typed program is never rejected with a spurious
type error, and a `BadArgType` is reported faithfully and only for a genuinely ill-typed
application. This file proves both:

* **Gradual permissiveness**: undeclared operators (`typeMismatch_undeclared`) and arguments
  beyond the declared arity (`typeCheckArgs_no_param`) are never rejected; an empty argument list
  is accepted (`typeCheckArgs_nil`); and `%Undefined%`/`Atom` unify with any type on the relevant
  side (`matchType_undefined_left/right`, `matchType_atom_left`). The checker fires only on a
  declared signature with a concrete, incompatible argument.
* **Faithful reporting**: when the checker reports a mismatch at position `pos`, the evaluator
  returns the corresponding `BadArgType` error and nothing else (`mettaEval_badArgType`). A
  `BadArgType` in the output corresponds to a checker rejection; the runtime does not invent type
  errors.
* **No false positives**: the *actual* type named in a `BadArgType` is a capture-avoiding
  freshening of a genuine type of the offending argument (`typeCheckArgs_act_real`), never
  invented.
* **Preservation (grounded core)**: arithmetic is closed on `Number` (`numBin_isNumber`),
  comparison yields `Bool` (`numCmp_isBool`), and `==` yields `Bool` or faithfully propagates an
  error (`eqAtom_isBoolOrError`). These ops carry exactly those declared signatures, so a
  well-typed grounded redex reduces to a value of its declared return type.

Together these cover progress (permissive and total) and preservation (grounded core, faithful and
non-fabricated errors) for the gradual and grounded fragment. Subject reduction over user-defined
`=`-rewriting, with a context-indexed typing judgment for rule variables, is proved in
`Proofs/Preservation.lean` (`WT.subst`, `reduction_preserves_type`).
-/

namespace Metta
open Metta.Minimal

/-! ## Ordered Cartesian choices -/

/-- Membership in the runtime's row-major Cartesian product is pointwise
membership in the corresponding input lists.  This deliberately states only
membership: `List.sections` has the same members but a different enumeration
order, while the evaluator's row-major order is semantically observable. -/
theorem mem_cartesian_iff_forall₂ {α : Type} {choices : List (List α)}
    {selection : List α} :
    selection ∈ cartesian choices ↔
      List.Forall₂ (fun selected candidates => selected ∈ candidates)
        selection choices := by
  induction choices generalizing selection with
  | nil => simp [cartesian]
  | cons candidates choices inductionHypothesis =>
      cases selection with
      | nil => simp [cartesian]
      | cons selected selection =>
          simp [cartesian, inductionHypothesis]

/-- **Gradual.** An operator whose runtime lookup yields only `%Undefined%` is never type-rejected:
the non-function candidate enables tuple evaluation and `typeMismatch` returns `none`. -/
theorem typeMismatch_undeclared (env : MinEnv) (w : World) (op : String) (args : List Atom)
    (h : getTypes env (typePrep w (Atom.sym op)) = [Atom.sym "%Undefined%"]) :
    typeMismatch env w op args = none := by
  simp [typeMismatch, selectFunctionType, h, scanFunctionTypeCandidates,
    FunctionTypeScanOutcome.markTupleEligible]

/-- `%Undefined%` as the *expected* type matches any actual type (gradual top). -/
theorem matchType_undefined_left (tb : Bindings) (actual : Atom) :
    matchType tb (Atom.sym "%Undefined%") actual = some tb := by
  have hc : (Atom.sym "%Undefined%" == Atom.sym "%Undefined%") = true := by decide
  simp [matchType, hc]

/-- `Atom` as the *expected* type matches any actual type (an `Atom`-typed parameter accepts
anything, which is what keeps quoted/unevaluated arguments well-typed). -/
theorem matchType_atom_left (tb : Bindings) (actual : Atom) :
    matchType tb (Atom.sym "Atom") actual = some tb := by
  have hc : (Atom.sym "Atom" == Atom.sym "Atom") = true := by decide
  simp [matchType, hc]

/-- `%Undefined%` as the *actual* type matches any expected type (an un-typed argument is accepted
everywhere). -/
theorem matchType_undefined_right (tb : Bindings) (expected : Atom) :
    matchType tb expected (Atom.sym "%Undefined%") = some tb := by
  have hc : (Atom.sym "%Undefined%" == Atom.sym "%Undefined%") = true := by decide
  simp [matchType, hc]

/-- `Atom` as the *actual* type also matches any expected type: the gradual top is **symmetric**.
Hyperon's `match_types` tests `type2 == ATOM_TYPE_ATOM` as well (`interpreter.rs:1225`), so a value of
meta-type `Atom` (e.g. a quoted/unevaluated argument) is accepted against any declared parameter. The
companion of `matchType_atom_left`. -/
theorem matchType_atom_right (tb : Bindings) (expected : Atom) :
    matchType tb expected (Atom.sym "Atom") = some tb := by
  have hc : (Atom.sym "Atom" == Atom.sym "Atom") = true := by decide
  simp [matchType, hc]

/-- Scanning a nonempty actual-type list against the gradual `Atom` formal selects the first
candidate, preserves the incoming private theory, and records no latent failures. -/
theorem scanActualTypes_atom_of_ne_nil (tb : Bindings) (actuals : List Atom)
    (hne : actuals ≠ []) :
    scanActualTypes tb (Atom.sym "Atom") actuals = ⟨some tb, []⟩ := by
  induction actuals with
  | nil => exact False.elim (hne rfl)
  | cons actual rest ih =>
      cases rest with
      | nil => simp [scanActualTypes, matchType_atom_left]
      | cons next tail =>
          have htail := ih (by simp)
          rw [scanActualTypes, htail]
          simp [matchType_atom_left]

/-- The `%Undefined%` formal has the same complete-scan behavior as `Atom`: every actual
candidate succeeds, so no latent type error is manufactured. -/
theorem scanActualTypes_undefined_of_ne_nil (tb : Bindings) (actuals : List Atom)
    (hne : actuals ≠ []) :
    scanActualTypes tb (Atom.sym "%Undefined%") actuals = ⟨some tb, []⟩ := by
  induction actuals with
  | nil => exact False.elim (hne rfl)
  | cons actual rest ih =>
      cases rest with
      | nil => simp [scanActualTypes, matchType_undefined_left]
      | cons next tail =>
          have htail := ih (by simp)
          rw [scanActualTypes, htail]
          simp [matchType_undefined_left]

/-- Literal gradual formals (`Atom` and `%Undefined%`) accept every nonempty ordered actual-type
list, preserve the incoming private theory, and record no latent failures. -/
theorem scanActualTypes_gradual_of_ne_nil (tb : Bindings) (formal : Atom)
    (actuals : List Atom)
    (hGradual : formal = Atom.sym "Atom" ∨ formal = Atom.sym "%Undefined%")
    (hne : actuals ≠ []) :
    scanActualTypes tb formal actuals = ⟨some tb, []⟩ := by
  rcases hGradual with rfl | rfl
  · exact scanActualTypes_atom_of_ne_nil tb actuals hne
  · exact scanActualTypes_undefined_of_ne_nil tb actuals hne

/-- A successful match anywhere in the ordered actual-type list guarantees that the complete scan
selects some binding presentation. The selected presentation remains the first success; this lemma
intentionally exposes only the existence needed by success-only consumers. -/
theorem scanActualTypes_selected_some_of_mem_match
    (tb : Bindings) (formal : Atom) (actuals : List Atom)
    (actual : Atom) (output : Bindings)
    (hmem : actual ∈ actuals)
    (hmatch : matchType tb formal actual = some output) :
    ∃ selected, (scanActualTypes tb formal actuals).selected = some selected := by
  induction actuals with
  | nil => simp at hmem
  | cons head tail ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨output, by simp [scanActualTypes, hmatch]⟩
      · rcases ih hmem with ⟨selected, hselected⟩
        cases hhead : matchType tb formal head with
        | none => exact ⟨selected, by simp [scanActualTypes, hhead, hselected]⟩
        | some headOutput =>
            exact ⟨headOutput, by simp [scanActualTypes, hhead]⟩

theorem typeCheckArgs_nil (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) : typeCheckArgs env w argTypes i tb [] = none := by
  simp [typeCheckArgs, typeCheckArgsOutcome, typeCheckArgsDetailedOutcome,
    typeCheckArgsDetailedOutcomeScoped]

/-- The compatibility argument checker reports success exactly when the detailed checker succeeds
with the same output bindings.  The existential latent-error ledger is intentionally retained in
this interface: consumers that inspect diagnostics must use the detailed witness rather than the
compatibility projection. -/
theorem typeCheckArgsOutcome_eq_success_iff
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb output : Bindings) (args : List Atom) :
    typeCheckArgsOutcome env w argTypes i tb args = .success output ↔
      ∃ latentErrors,
        typeCheckArgsDetailedOutcome env w argTypes i tb args =
          .success output latentErrors := by
  cases hDetailed : typeCheckArgsDetailedOutcome env w argTypes i tb args <;>
    simp [typeCheckArgsOutcome, hDetailed]

/-- Characterize selection from a singleton arrow declaration without exposing the candidate-scan
implementation to downstream proofs.  Exact arity is shared by every public selector; successful
detailed checking supplies both the selected private
theory and its (intentionally discarded) latent-error ledger. -/
theorem selectFunctionType_singleton_arrow_selected
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (returnType : Atom) (typeBindings : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hCheck : typeCheckArgsDetailedOutcome env w argTypes 0 [] args =
      .success typeBindings latentErrors) :
    selectFunctionType env w (.sym op) args =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } := by
  unfold selectFunctionType
  rw [hTypes]
  simp [scanFunctionTypeCandidates, hArity, hCheck]

/-- Success-only compatibility corollary of
`selectFunctionType_singleton_arrow_selected`.  This is appropriate precisely at selection
boundaries, where a successful candidate discards its latent diagnostic ledger; consumers that
reason about exhausted scans must retain the detailed outcome instead. -/
theorem selectFunctionType_singleton_arrow_selected_of_outcome
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (returnType : Atom) (typeBindings : Bindings)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hCheck : typeCheckArgsOutcome env w argTypes 0 [] args =
      .success typeBindings) :
    selectFunctionType env w (.sym op) args =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } := by
  obtain ⟨latentErrors, hDetailed⟩ :=
    (typeCheckArgsOutcome_eq_success_iff env w argTypes 0 [] typeBindings args).mp hCheck
  exact selectFunctionType_singleton_arrow_selected env w op args argTypes returnType
    typeBindings latentErrors hTypes hArity hDetailed

/-- Characterize expected-return-aware selection from one raw declaration
after the selector gives it a private arrow presentation.  The interface
keeps signature localization, the complete branch search, and return-gate
ledgers visible without exposing the ordered candidate scanner. -/
theorem selectFunctionTypeForExpected_singleton_fresh_arrow_selected
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (rawCandidate returnType expected : Atom) (typeBindings : Bindings)
    (branches : List Bindings) (argumentErrors : List TypeCheckArgsError)
    (returnErrors : List ExpectedFunctionTypeError)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [rawCandidate])
    (hFresh : freshenFunctionTypeCandidates env
        (.expr (.sym op :: args)) args expected [rawCandidate] =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hArgs : typeCheckArgsBranchesScoped env w argTypes
        (applicationTypeInferenceScope expected args) 0 [] args =
      ⟨branches, argumentErrors⟩)
    (hReturn : scanExpectedReturnBranches expected returnType branches =
      ⟨some typeBindings, returnErrors⟩) :
    selectFunctionTypeForExpected env w (.sym op) args expected =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } := by
  simp only [selectFunctionTypeForExpected,
    selectFunctionTypeForExpectedAvoiding, hTypes]
  change scanFunctionTypeCandidatesForExpected env w
      (.expr (.sym op :: args)) args expected false
        (freshenFunctionTypeCandidates env (.expr (.sym op :: args)) args
          expected [rawCandidate]) = _
  rw [hFresh]
  simp [scanFunctionTypeCandidatesForExpected, hArity, hArgs, hReturn]

/-- Stable-signature specialization of
`selectFunctionTypeForExpected_singleton_fresh_arrow_selected`.  The added
equation is intentional: polymorphic signatures are generally alpha-freshened
and therefore cannot be claimed to remain syntactically unchanged. -/
theorem selectFunctionTypeForExpected_singleton_arrow_selected
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (returnType expected : Atom) (typeBindings : Bindings)
    (branches : List Bindings) (argumentErrors : List TypeCheckArgsError)
    (returnErrors : List ExpectedFunctionTypeError)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hFresh : freshenFunctionTypeCandidates env
        (.expr (.sym op :: args)) args expected
        [.expr (.sym "->" :: argTypes ++ [returnType])] =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hArgs : typeCheckArgsBranchesScoped env w argTypes
        (applicationTypeInferenceScope expected args) 0 [] args =
      ⟨branches, argumentErrors⟩)
    (hReturn : scanExpectedReturnBranches expected returnType branches =
      ⟨some typeBindings, returnErrors⟩) :
    selectFunctionTypeForExpected env w (.sym op) args expected =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } :=
  selectFunctionTypeForExpected_singleton_fresh_arrow_selected
    env w op args argTypes
      (.expr (.sym "->" :: argTypes ++ [returnType])) returnType expected
      typeBindings branches argumentErrors returnErrors hTypes hFresh hArity
      hArgs hReturn

/-- Seeding expected-aware applicability with the empty theory recovers the
    compatibility scanner exactly.  This is the boundary used by closed
    evaluator lemmas; live-binding evaluation uses the seeded scanner
    directly. -/
theorem scanFunctionTypeCandidatesForExpectedFrom_empty
    (env : MinEnv) (w : World) (expression : Atom) (args : List Atom)
    (expected : Atom) (allowExtraArgs : Bool) (candidates : List Atom) :
    scanFunctionTypeCandidatesForExpectedFrom env w expression args expected
        allowExtraArgs [] candidates =
      scanFunctionTypeCandidatesForExpected env w expression args expected
        allowExtraArgs candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate candidates ih =>
      cases candidate with
      | sym | var | gnd =>
          simp [scanFunctionTypeCandidatesForExpectedFrom,
            scanFunctionTypeCandidatesForExpected, ih]
      | expr atoms =>
          cases atoms with
          | nil =>
              simp [scanFunctionTypeCandidatesForExpectedFrom,
                scanFunctionTypeCandidatesForExpected, ih]
          | cons head signature =>
          cases head <;>
                simp [scanFunctionTypeCandidatesForExpectedFrom,
                  scanFunctionTypeCandidatesForExpected,
                  applicationTypeInferenceScopeFrom, Bindings.vars, ih]

/-- Closed compatibility form of seeded expected-aware selection. -/
theorem selectFunctionTypeForExpectedFrom_empty
    (env : MinEnv) (w : World) (operator : Atom) (args : List Atom)
    (expected : Atom) :
    selectFunctionTypeForExpectedFrom env w operator args expected [] =
      selectFunctionTypeForExpectedAvoiding env w operator args expected [] := by
  simp [selectFunctionTypeForExpectedFrom,
    selectFunctionTypeForExpectedAvoiding,
    scanFunctionTypeCandidatesForExpectedFrom_empty, Bindings.vars]

/-- The compatibility actual-type scan selects exactly the head of the complete branch list.  This
is the structural bridge between the historical first-success view and repaired branch-valued
applicability; it does not discard the remaining branches or their diagnostics. -/
theorem scanActualTypes_selected_eq_branches_head
    (tb : Bindings) (expected : Atom) (actuals : List Atom) :
    (scanActualTypes tb expected actuals).selected =
      (scanActualTypeBranches tb expected actuals).successes.head? := by
  induction actuals with
  | nil => rfl
  | cons actual actuals ih =>
      simp only [scanActualTypes, scanActualTypeBranches]
      split <;> simp_all

/-- Under one fixed application scope, detailed first-success checking and
complete branch search agree on the first successful presentation.  Later
branches remain available to expected-return backtracking. -/
theorem typeCheckArgsBranchesScoped_head_of_detailed_success
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (boundaryScope : List VarName) (tb : Bindings) (args : List Atom)
    (output : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hDetailed : typeCheckArgsDetailedOutcomeScoped env w argTypes
      boundaryScope i tb args =
      .success output latentErrors) :
    (typeCheckArgsBranchesScoped env w argTypes boundaryScope i tb args).successes.head? =
      some output := by
  induction args generalizing i tb output latentErrors with
  | nil =>
      simp [typeCheckArgsDetailedOutcomeScoped] at hDetailed
      simp_all [typeCheckArgsBranchesScoped]
  | cons ai more ih =>
      simp only [typeCheckArgsDetailedOutcomeScoped] at hDetailed
      simp only [typeCheckArgsBranchesScoped]
      split at hDetailed
      · simp_all
      · rename_i ti _hti
        generalize hselected :
            (scanActualTypes tb ti
              ((getTypes env (typePrep w ai)).map
                  (freshenTypeCandidate
                  (boundaryScope ++ typeInferenceAvoid env (.expr (ai :: more))
                    (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i))).selected =
              selectedOption at hDetailed
        cases selectedOption with
        | none =>
            generalize herrors :
                List.map (fun actual =>
                  ({ position := i + 1, expected := instantiate tb ti, actual := actual } :
                    TypeCheckArgsError))
                  (scanActualTypes tb ti
                    ((getTypes env (typePrep w ai)).map
                      (freshenTypeCandidate
                        (boundaryScope ++ typeInferenceAvoid env (.expr (ai :: more))
                          (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i))).failures =
                  currentErrors at hDetailed
            cases currentErrors <;> cases hDetailed
        | some selected =>
            generalize htail :
                typeCheckArgsDetailedOutcomeScoped env w argTypes
                  boundaryScope (i + 1) selected more =
                  tailOutcome at hDetailed
            cases tailOutcome with
            | failure firstError laterErrors => simp [htail] at hDetailed
            | success tailOutput tailErrors =>
                simp [htail] at hDetailed
                rcases hDetailed with ⟨rfl, rfl⟩
                have hscanHead :
                    (scanActualTypeBranches tb ti
                      ((getTypes env (typePrep w ai)).map
                        (freshenTypeCandidate
                          (boundaryScope ++ typeInferenceAvoid env (.expr (ai :: more))
                            (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i))).successes.head? =
                      some selected := by
                  rw [← scanActualTypes_selected_eq_branches_head]
                  exact hselected
                generalize hsuccesses :
                    (scanActualTypeBranches tb ti
                      ((getTypes env (typePrep w ai)).map
                        (freshenTypeCandidate
                          (boundaryScope ++ typeInferenceAvoid env (.expr (ai :: more))
                            (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i))).successes =
                      successes at hscanHead ⊢
                cases successes with
                | nil => simp at hscanHead
                | cons head rest =>
                    simp at hscanHead
                    subst head
                    simp only [List.map_cons, List.flatMap_cons]
                    have htailHead := ih (i := i + 1) (tb := selected)
                      (output := tailOutput) (latentErrors := tailErrors) htail
                    have htailNonempty :
                        (typeCheckArgsBranchesScoped env w argTypes boundaryScope
                          (i + 1) selected more).successes ≠
                          [] := by
                      intro hempty
                      rw [hempty] at htailHead
                      simp at htailHead
                    rw [List.head?_append_of_ne_nil _ htailNonempty]
                    exact htailHead

/-- Ordinary checking is the scope-specialized corollary of the fixed-scope
head agreement theorem. -/
theorem typeCheckArgsBranches_head_of_detailed_success
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (args : List Atom) (output : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hDetailed : typeCheckArgsDetailedOutcome env w argTypes i tb args =
      .success output latentErrors) :
    (typeCheckArgsBranches env w argTypes i tb args).successes.head? =
      some output := by
  exact typeCheckArgsBranchesScoped_head_of_detailed_success env w argTypes i
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") args) tb args
      output latentErrors hDetailed

/-- Singleton expected-return selection reuses the same complete selected
policy whenever the expected-scope detailed scan succeeds and the return
gate preserves that private theory. -/
theorem selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (returnType expected : Atom) (typeBindings : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hFresh : freshenFunctionTypeCandidates env
        (.expr (.sym op :: args)) args expected
        [.expr (.sym "->" :: argTypes ++ [returnType])] =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hCheck : typeCheckArgsDetailedOutcomeScoped env w argTypes
        (applicationTypeInferenceScope expected args) 0 [] args =
      .success typeBindings latentErrors)
    (hReturn : matchType typeBindings expected returnType = some typeBindings) :
    selectFunctionTypeForExpected env w (.sym op) args expected =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } := by
  have hHead := typeCheckArgsBranchesScoped_head_of_detailed_success
    env w argTypes 0 (applicationTypeInferenceScope expected args) [] args
      typeBindings latentErrors hCheck
  cases hBranches : typeCheckArgsBranchesScoped env w argTypes
      (applicationTypeInferenceScope expected args) 0 [] args with
  | mk successes argumentErrors =>
      have hHead' : successes.head? = some typeBindings := by
        simpa [hBranches] using hHead
      cases successes with
      | nil => simp at hHead'
      | cons head rest =>
          simp at hHead'
          subst head
          apply selectFunctionTypeForExpected_singleton_arrow_selected
            env w op args argTypes returnType expected typeBindings
            (typeBindings :: rest) argumentErrors [] hTypes hFresh hArity hBranches
          simp [scanExpectedReturnBranches, hReturn]

/-- Live-theory counterpart of
`selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed`.
Applicability starts from `initialBindings`, protects that scope while
freshening the arrow, and returns the complete selected theory. -/
theorem selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
    (env : MinEnv) (w : World) (op : String) (args argTypes : List Atom)
    (returnType expected : Atom) (initialBindings typeBindings : Bindings)
    (latentErrors : List TypeCheckArgsError)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hFresh : freshenFunctionTypeCandidatesAvoiding env
        (.expr (.sym op :: args)) args expected initialBindings.vars
        [.expr (.sym "->" :: argTypes ++ [returnType])] =
      [.expr (.sym "->" :: argTypes ++ [returnType])])
    (hArity : args.length = argTypes.length)
    (hCheck : typeCheckArgsDetailedOutcomeScoped env w argTypes
        (applicationTypeInferenceScopeFrom expected args initialBindings)
        0 initialBindings args = .success typeBindings latentErrors)
    (hReturn : matchType typeBindings expected returnType = some typeBindings) :
    selectFunctionTypeForExpectedFrom env w (.sym op) args expected
        initialBindings =
      .selected
        { functionType := .expr (.sym "->" :: argTypes ++ [returnType])
          argumentTypes := argTypes
          returnType := returnType
          typeBindings := typeBindings } := by
  have hHead := typeCheckArgsBranchesScoped_head_of_detailed_success
    env w argTypes 0
      (applicationTypeInferenceScopeFrom expected args initialBindings)
      initialBindings args typeBindings latentErrors hCheck
  cases hBranches : typeCheckArgsBranchesScoped env w argTypes
      (applicationTypeInferenceScopeFrom expected args initialBindings)
      0 initialBindings args with
  | mk successes argumentErrors =>
      have hHead' : successes.head? = some typeBindings := by
        simpa [hBranches] using hHead
      cases successes with
      | nil => simp at hHead'
      | cons head rest =>
          simp at hHead'
          subst head
          simp only [selectFunctionTypeForExpectedFrom, hTypes]
          change scanFunctionTypeCandidatesForExpectedFrom env w
              (.expr (.sym op :: args)) args expected false initialBindings
              (freshenFunctionTypeCandidatesAvoiding env
                (.expr (.sym op :: args)) args expected initialBindings.vars
                [.expr (.sym "->" :: argTypes ++ [returnType])]) = _
          rw [hFresh]
          simp [scanFunctionTypeCandidatesForExpectedFrom, hArity, hBranches,
            scanExpectedReturnBranches, hReturn]

/-- **Gradual.** An argument in a position beyond the declared parameters is not checked; extra
arguments never cause a type error. -/
theorem typeCheckArgs_no_param (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (ai : Atom) (more : List Atom) (h : argTypes[i]? = none) :
    typeCheckArgs env w argTypes i tb (ai :: more) = none := by
  simp [typeCheckArgs, typeCheckArgsOutcome, typeCheckArgsDetailedOutcome,
    typeCheckArgsDetailedOutcomeScoped, h]

/-- Every diagnostic emitted by function-type selection has the published
`(Error source message)` shape. -/
@[simp] theorem FunctionTypeError.toAtom_isError
    (expression : Atom) (error : FunctionTypeError) :
    (error.toAtom expression).isError = true := by
  cases error <;> rfl

/-- Every diagnostic emitted by the live-theory selected-application scan has
the published error shape. -/
@[simp] theorem ExpectedFunctionTypeError.toAtom_isError
    (expression : Atom) (error : ExpectedFunctionTypeError) :
    (error.toAtom expression).isError = true := by
  cases error with
  | ordinary error => simp [ExpectedFunctionTypeError.toAtom]
  | badReturn expected actual => rfl

/-- Every retained type-scan failure is emitted, in order, when no tuple path is available. -/
theorem mettaEval_typeErrors (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (op : String) (args : List Atom) (errors : List ExpectedFunctionTypeError)
    (hinst : instantiate bnd (Atom.expr (Atom.sym op :: args)) =
      Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hscan : selectFunctionTypeForExpectedFrom env st.world (Atom.sym op) args
        (Atom.sym "%Undefined%") bnd =
      .exhausted errors false) :
    mettaEval env (fuel + 1) st bnd (Atom.expr (Atom.sym op :: args)) =
      (errors.map (fun error =>
        (error.toAtom (Atom.expr (Atom.sym op :: args)), bnd)), st) := by
  have hNotEmpty :
      ((Atom.expr (Atom.sym op :: args) : Atom) == emptyA) = false := rfl
  conv_lhs => unfold mettaEval
  rw [hinst]
  simp only [hNotEmpty, hNotError, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte]
  rw [executeApplicationPlan, hscan]
  simp [prioritizeSemanticResults]

/-- **Faithful error reporting.** When the gradual checker flags a mismatch at position `pos`
(expected `exp`, actual `act`), one evaluation step of `(op args)` returns the corresponding
`BadArgType` error and nothing else. A `BadArgType` in the output corresponds to a checker
rejection; the runtime never invents a type error. -/
theorem mettaEval_badArgType (env : MinEnv) (fuel : Nat) (st : St) (bnd : Bindings)
    (op : String) (args : List Atom) (pos : Nat) (exp act : Atom)
    (hinst : instantiate bnd (Atom.expr (Atom.sym op :: args)) = Atom.expr (Atom.sym op :: args))
    (hNotError : (Atom.expr (Atom.sym op :: args)).isError = false)
    (hscan : selectFunctionTypeForExpectedFrom env st.world (Atom.sym op) args
        (Atom.sym "%Undefined%") bnd =
      .exhausted [.ordinary (.badArgument pos exp act)] false) :
    mettaEval env (fuel + 1) st bnd (Atom.expr (Atom.sym op :: args)) =
      ([(Atom.expr [Atom.sym "Error", Atom.expr (Atom.sym op :: args),
          Atom.expr [Atom.sym "BadArgType", Atom.gnd (Ground.int (Int.ofNat pos)), exp, act]], bnd)], st) := by
  simpa [ExpectedFunctionTypeError.toAtom, FunctionTypeError.toAtom] using
    mettaEval_typeErrors env fuel st bnd op args
      [.ordinary (.badArgument pos exp act)] hinst hNotError hscan

/-- **Totality of typing.** `getTypes` assigns at least one type to every atom; gradual typing has
no "untyped gap": an undeclared symbol gets `%Undefined%`, an application its inferred return type(s)
or `%Undefined%`, never the empty set. (Proved by the generated functional-induction principle.) -/
theorem getTypes_ne_nil (env : MinEnv) (a : Atom) : getTypes env a ≠ [] := by
  fun_induction getTypes env a <;>
    simp_all <;> (try split) <;> simp_all <;> (try split) <;> simp_all

/-- A contiguous run of `Atom` formals accepts every corresponding argument without changing the
private type theory or accumulating latent failures.  The theorem is index-parametric so callers
can use it inside larger signatures rather than re-proving fixed arities. -/
theorem typeCheckArgsDetailedOutcomeScoped_all_atom
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (boundaryScope : List VarName) (tb : Bindings) (args : List Atom)
    (hAtom : ∀ j, j < args.length →
      argTypes[i + j]? = some (Atom.sym "Atom")) :
    typeCheckArgsDetailedOutcomeScoped env w argTypes boundaryScope i tb args =
      .success tb [] := by
  induction args generalizing i tb with
  | nil => simp [typeCheckArgsDetailedOutcomeScoped]
  | cons argument rest ih =>
      have hHead : argTypes[i]? = some (Atom.sym "Atom") := by
        simpa using hAtom 0 (by simp)
      rw [typeCheckArgsDetailedOutcomeScoped, hHead]
      simp only
      let actuals :=
        (getTypes env (typePrep w argument)).map
          (freshenTypeCandidate
            (boundaryScope ++ typeInferenceAvoid env (Atom.expr (argument :: rest))
              (argTypes ++ getTypes env (typePrep w argument)) ++ tb.vars)
            i)
      have hActuals : actuals ≠ [] := by
        simp [actuals, getTypes_ne_nil env (typePrep w argument)]
      rw [scanActualTypes_atom_of_ne_nil tb actuals hActuals]
      simp only
      have hTail := ih (i + 1) tb (by
        intro j hj
        have hj' : Nat.succ j < Nat.succ rest.length := Nat.succ_lt_succ hj
        have h := hAtom (j + 1) (by
          simpa [Nat.succ_eq_add_one] using hj')
        have hidx : (i + 1) + j = i + (j + 1) := by omega
        rw [hidx]
        exact h)
      rw [hTail]
      rfl

/-- Ordinary all-`Atom` checking is the complete-source-scope specialization
of `typeCheckArgsDetailedOutcomeScoped_all_atom`. -/
theorem typeCheckArgsDetailedOutcome_all_atom
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (args : List Atom)
    (hAtom : ∀ j, j < args.length →
      argTypes[i + j]? = some (Atom.sym "Atom")) :
    typeCheckArgsDetailedOutcome env w argTypes i tb args =
      .success tb [] :=
  typeCheckArgsDetailedOutcomeScoped_all_atom env w argTypes i
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") args) tb args
      hAtom

/-- One gradual formal followed by a successful tail preserves both the private theory and the
empty latent-error ledger. This is the stable boundary lemma for argument lists containing literal
`Atom` or `%Undefined%` positions. -/
theorem typeCheckArgsDetailedOutcomeScoped_cons_gradual
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (boundaryScope : List VarName) (tb : Bindings) (argument : Atom)
    (rest : List Atom) (formal : Atom)
    (hHead : argTypes[i]? = some formal)
    (hGradual : formal = Atom.sym "Atom" ∨ formal = Atom.sym "%Undefined%")
    (hTail : typeCheckArgsDetailedOutcomeScoped env w argTypes boundaryScope
      (i + 1) tb rest =
      .success tb []) :
    typeCheckArgsDetailedOutcomeScoped env w argTypes boundaryScope i tb
      (argument :: rest) =
      .success tb [] := by
  rw [typeCheckArgsDetailedOutcomeScoped, hHead]
  simp only
  let actuals :=
    (getTypes env (typePrep w argument)).map
      (freshenTypeCandidate
        (boundaryScope ++ typeInferenceAvoid env (Atom.expr (argument :: rest))
          (argTypes ++ getTypes env (typePrep w argument)) ++ tb.vars)
        i)
  have hActuals : actuals ≠ [] := by
    simp [actuals, getTypes_ne_nil env (typePrep w argument)]
  rw [scanActualTypes_gradual_of_ne_nil tb formal actuals hGradual hActuals]
  simp only
  rw [hTail]
  rfl

/-- Pointwise literal gradual formals accept an aligned argument list without changing the
private type theory. The indexed hypothesis lets this theorem compose inside larger arrows. -/
theorem typeCheckArgsDetailedOutcomeScoped_all_gradual
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (boundaryScope : List VarName) (tb : Bindings) (args : List Atom)
    (hGradual : ∀ j, j < args.length →
      argTypes[i + j]? = some (Atom.sym "Atom") ∨
      argTypes[i + j]? = some (Atom.sym "%Undefined%")) :
    typeCheckArgsDetailedOutcomeScoped env w argTypes boundaryScope i tb args =
      .success tb [] := by
  induction args generalizing i tb with
  | nil => simp [typeCheckArgsDetailedOutcomeScoped]
  | cons argument rest ih =>
      rcases hGradual 0 (by simp) with hHead | hHead
      · have hHead' : argTypes[i]? = some (Atom.sym "Atom") := by
          simpa using hHead
        apply typeCheckArgsDetailedOutcomeScoped_cons_gradual env w argTypes i
          boundaryScope tb argument rest (Atom.sym "Atom") hHead' (Or.inl rfl)
        apply ih
        intro j hj
        have hj' : Nat.succ j < Nat.succ rest.length := Nat.succ_lt_succ hj
        have h := hGradual (j + 1) (by
          simpa [Nat.succ_eq_add_one] using hj')
        have hidx : (i + 1) + j = i + (j + 1) := by omega
        simpa only [hidx] using h
      · have hHead' : argTypes[i]? = some (Atom.sym "%Undefined%") := by
          simpa using hHead
        apply typeCheckArgsDetailedOutcomeScoped_cons_gradual env w argTypes i
          boundaryScope tb argument rest (Atom.sym "%Undefined%") hHead'
          (Or.inr rfl)
        apply ih
        intro j hj
        have hj' : Nat.succ j < Nat.succ rest.length := Nat.succ_lt_succ hj
        have h := hGradual (j + 1) (by
          simpa [Nat.succ_eq_add_one] using hj')
        have hidx : (i + 1) + j = i + (j + 1) := by omega
        simpa only [hidx] using h

/-- Ordinary gradual checking is the complete-source-scope specialization
of the fixed-scope fold. -/
theorem typeCheckArgsDetailedOutcome_all_gradual
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (args : List Atom)
    (hGradual : ∀ j, j < args.length →
      argTypes[i + j]? = some (Atom.sym "Atom") ∨
      argTypes[i + j]? = some (Atom.sym "%Undefined%")) :
    typeCheckArgsDetailedOutcome env w argTypes i tb args = .success tb [] :=
  typeCheckArgsDetailedOutcomeScoped_all_gradual env w argTypes i
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") args) tb args
      hGradual

/-- A first argument with at least one successful actual type, followed by literal gradual
formals, makes the compatibility checker succeed. Latent failures from non-selected actual types
are retained by the detailed checker and deliberately hidden only at this compatibility boundary. -/
theorem typeCheckArgsOutcome_cons_selected_gradual_tail
    (env : MinEnv) (w : World) (argTypes : List Atom) (i : Nat)
    (tb : Bindings) (argument : Atom) (rest : List Atom) (formal : Atom)
    (hHead : argTypes[i]? = some formal)
    (hSelected : ∃ output,
      (scanActualTypes tb formal
        ((getTypes env (typePrep w argument)).map
          (freshenTypeCandidate
            (applicationTypeInferenceScope (Atom.sym "%Undefined%")
                (argument :: rest) ++
              typeInferenceAvoid env (Atom.expr (argument :: rest))
              (argTypes ++ getTypes env (typePrep w argument)) ++ tb.vars)
            i))).selected = some output)
    (hGradual : ∀ j, j < rest.length →
      argTypes[(i + 1) + j]? = some (Atom.sym "Atom") ∨
      argTypes[(i + 1) + j]? = some (Atom.sym "%Undefined%")) :
    ∃ output,
      typeCheckArgsOutcome env w argTypes i tb (argument :: rest) =
        .success output := by
  rw [typeCheckArgsOutcome, typeCheckArgsDetailedOutcome,
    typeCheckArgsDetailedOutcomeScoped, hHead]
  simp only
  let actuals :=
    (getTypes env (typePrep w argument)).map
      (freshenTypeCandidate
        (applicationTypeInferenceScope (Atom.sym "%Undefined%")
            (argument :: rest) ++
          typeInferenceAvoid env (Atom.expr (argument :: rest))
          (argTypes ++ getTypes env (typePrep w argument)) ++ tb.vars)
        i)
  have hSelected' : ∃ output,
      (scanActualTypes tb formal actuals).selected = some output := by
    simpa [actuals] using hSelected
  cases hscan : scanActualTypes tb formal actuals with
  | mk selected failures =>
      cases selected with
      | none => simp [hscan] at hSelected'
      | some output =>
          have hTail := typeCheckArgsDetailedOutcomeScoped_all_gradual
            env w argTypes (i + 1)
              (applicationTypeInferenceScope (Atom.sym "%Undefined%")
                (argument :: rest))
              output rest hGradual
          simp only
          rw [hTail]
          exact ⟨output, rfl⟩

/-- Fixed-list detailed corollary for an all-`Atom` signature.  Unlike the compatibility
projection, this records that the successful scan accumulated no latent failures. -/
theorem typeCheckArgsDetailedOutcome_replicate_atom
    (env : MinEnv) (w : World) (args : List Atom) :
    typeCheckArgsDetailedOutcome env w
        (List.replicate args.length (Atom.sym "Atom")) 0 [] args =
      .success [] [] := by
  apply typeCheckArgsDetailedOutcome_all_atom env w _ 0 [] args
  intro j hj
  simp [hj]

/-- Compatibility projection of `typeCheckArgsDetailedOutcome_replicate_atom`. -/
theorem typeCheckArgsOutcome_replicate_atom
    (env : MinEnv) (w : World) (args : List Atom) :
    typeCheckArgsOutcome env w
        (List.replicate args.length (Atom.sym "Atom")) 0 [] args =
      .success [] := by
  rw [typeCheckArgsOutcome,
    typeCheckArgsDetailedOutcome_replicate_atom env w args]

/-- A singleton operator whose arguments are all quoted `Atom`s and whose result is `Bool` selects
the same empty private theory under the concrete expected type `Bool`. -/
theorem selectFunctionTypeForExpected_atom_args_bool_selected
    (env : MinEnv) (w : World) (op : String) (args : List Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])]) :
    selectFunctionTypeForExpected env w (.sym op) args (.sym "Bool") =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym "Bool"
          typeBindings := [] } := by
  apply selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed
    env w op args (List.replicate args.length (.sym "Atom")) (.sym "Bool")
      (.sym "Bool") [] [] hTypes
  · simp [freshenFunctionTypeCandidates,
      freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_atom env w _ 0
      (applicationTypeInferenceScope (.sym "Bool") args) [] args
    intro j hj
    simp [hj]
  · rfl

/-- A singleton symbolic arrow with only quoted `Atom` arguments remains
selected when ordinary evaluation asks for `%Undefined%`.  The result symbol
is arbitrary: gradual expectedness does not add a return constraint. -/
theorem selectFunctionTypeForExpectedFrom_atom_args_undefined_selected
    (env : MinEnv) (w : World) (op resultType : String) (args : List Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    selectFunctionTypeForExpectedFrom env w (.sym op) args
        (.sym "%Undefined%") [] =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym resultType])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym resultType
          typeBindings := [] } := by
  rw [selectFunctionTypeForExpectedFrom_empty]
  change selectFunctionTypeForExpected env w (.sym op) args
      (.sym "%Undefined%") = _
  apply selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed
    env w op args (List.replicate args.length (.sym "Atom"))
      (.sym resultType) (.sym "%Undefined%") [] [] hTypes
  · simp [freshenFunctionTypeCandidates,
      freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_atom env w _ 0
      (applicationTypeInferenceScope (.sym "%Undefined%") args) [] args
    intro j hj
    simp [hj]
  · exact matchType_undefined_left [] (.sym resultType)

/-- Live-binding specialization of
`selectFunctionTypeForExpectedFrom_atom_args_undefined_selected`.  Quoted
`Atom` formals and gradual expected return leave the incoming theory
unchanged, so the selected payload records it exactly. -/
theorem selectFunctionTypeForExpectedFrom_atom_args_undefined_selected_from
    (env : MinEnv) (w : World) (op resultType : String) (args : List Atom)
    (initialBindings : Bindings)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    selectFunctionTypeForExpectedFrom env w (.sym op) args
        (.sym "%Undefined%") initialBindings =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym resultType])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym resultType
          typeBindings := initialBindings } := by
  apply selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
    env w op args (List.replicate args.length (.sym "Atom"))
      (.sym resultType) (.sym "%Undefined%") initialBindings initialBindings []
      hTypes
  · simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_atom env w _ 0
      (applicationTypeInferenceScopeFrom (.sym "%Undefined%") args
        initialBindings) initialBindings args
    intro j hj
    simp [hj]
  · exact matchType_undefined_left initialBindings (.sym resultType)

/-- Ordinary-selection twin of
`selectFunctionTypeForExpectedFrom_atom_args_undefined_selected`, generalized
over the symbolic result type. -/
theorem selectFunctionType_atom_args_symbolic_return_selected
    (env : MinEnv) (w : World) (op resultType : String) (args : List Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym resultType])]) :
    selectFunctionType env w (.sym op) args =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym resultType])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym resultType
          typeBindings := [] } := by
  exact selectFunctionType_singleton_arrow_selected env w op args
    (List.replicate args.length (.sym "Atom")) (.sym resultType) [] [] hTypes
    (by simp) (typeCheckArgsDetailedOutcome_replicate_atom env w args)

/-- The concrete `let` policy remains selected under ordinary
`%Undefined%` expectedness.  Its payload is evaluated while its pattern and
template are quoted, and the scan accumulates no private bindings. -/
theorem selectFunctionTypeForExpectedFrom_let_policy_selected
    (env : MinEnv) (w : World) (op : String)
    (pattern payload template : Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    selectFunctionTypeForExpectedFrom env w (.sym op)
        [pattern, payload, template] (.sym "%Undefined%") [] =
      .selected
        { functionType := .expr
            [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
              .sym "%Undefined%"]
          argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
          returnType := .sym "%Undefined%"
          typeBindings := [] } := by
  rw [selectFunctionTypeForExpectedFrom_empty]
  change selectFunctionTypeForExpected env w (.sym op)
      [pattern, payload, template] (.sym "%Undefined%") = _
  apply selectFunctionTypeForExpected_singleton_arrow_selected_of_detailed
    env w op [pattern, payload, template]
      [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      (.sym "%Undefined%") (.sym "%Undefined%") [] [] hTypes
  · simp [freshenFunctionTypeCandidates,
      freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_gradual
    intro j hj
    simp at hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl <;> simp
  · exact matchType_undefined_left [] (.sym "%Undefined%")

/-- Live-binding form of `selectFunctionTypeForExpectedFrom_let_policy_selected`.
The gradual argument and return positions preserve the complete incoming
theory while the closed arrow remains spelling-invariant under freshening. -/
theorem selectFunctionTypeForExpectedFrom_let_policy_selected_from
    (env : MinEnv) (w : World) (op : String)
    (pattern payload template : Atom) (initialBindings : Bindings)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    selectFunctionTypeForExpectedFrom env w (.sym op)
        [pattern, payload, template] (.sym "%Undefined%") initialBindings =
      .selected
        { functionType := .expr
            [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
              .sym "%Undefined%"]
          argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
          returnType := .sym "%Undefined%"
          typeBindings := initialBindings } := by
  apply selectFunctionTypeForExpectedFrom_singleton_arrow_selected_of_detailed
    env w op [pattern, payload, template]
      [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      (.sym "%Undefined%") (.sym "%Undefined%") initialBindings
      initialBindings [] hTypes
  · simp [freshenFunctionTypeCandidatesAvoiding, freshenTypeCandidate,
      renameAllVars]
  · simp
  · apply typeCheckArgsDetailedOutcomeScoped_all_gradual
    intro j hj
    simp at hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl <;> simp
  · exact matchType_undefined_left initialBindings (.sym "%Undefined%")

/-- Ordinary-selection twin of
`selectFunctionTypeForExpectedFrom_let_policy_selected`. -/
theorem selectFunctionType_let_policy_selected
    (env : MinEnv) (w : World) (op : String)
    (pattern payload template : Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
        .sym "%Undefined%"]]) :
    selectFunctionType env w (.sym op) [pattern, payload, template] =
      .selected
        { functionType := .expr
            [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom",
              .sym "%Undefined%"]
          argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
          returnType := .sym "%Undefined%"
          typeBindings := [] } := by
  apply selectFunctionType_singleton_arrow_selected
    env w op [pattern, payload, template]
      [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      (.sym "%Undefined%") [] [] hTypes (by simp)
  apply typeCheckArgsDetailedOutcome_all_gradual
  intro j hj
  simp at hj
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl | rfl <;> simp

/-- Ordinary-selection twin of `selectFunctionTypeForExpected_atom_args_bool_selected`. -/
theorem selectFunctionType_atom_args_bool_selected
    (env : MinEnv) (w : World) (op : String) (args : List Atom)
    (hTypes : getTypes env (typePrep w (.sym op)) =
      [.expr (.sym "->" ::
        List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])]) :
    selectFunctionType env w (.sym op) args =
      .selected
        { functionType := .expr (.sym "->" ::
            List.replicate args.length (.sym "Atom") ++ [.sym "Bool"])
          argumentTypes := List.replicate args.length (.sym "Atom")
          returnType := .sym "Bool"
          typeBindings := [] } := by
  exact selectFunctionType_singleton_arrow_selected env w op args
    (List.replicate args.length (.sym "Atom")) (.sym "Bool") [] [] hTypes
    (by simp) (typeCheckArgsDetailedOutcome_replicate_atom env w args)

/-- `getTypes` is a function, so any two computed type lists for the same atom are the same up to
permutation. This is the theorem-level uniqueness surface available before introducing a separate
relational type-synthesis judgment. -/
theorem getTypes_unique_modulo_permutation (env : MinEnv) (a : Atom) {ts₁ ts₂ : List Atom}
    (h₁ : getTypes env a = ts₁) (h₂ : getTypes env a = ts₂) : ts₁.Perm ts₂ := by
  rw [← h₁, ← h₂]

/-- One selected runtime type candidate is the capture-avoiding alpha-presentation of a raw
`getTypes` candidate.  The finite avoid set and inference position affect only private variable
spellings. -/
def TypeCandidateFresheningRel (raw observed : Atom) : Prop :=
  ∃ avoid position, observed = freshenTypeCandidate avoid position raw

/-- Every failed actual retained by the full scan came from its input list. -/
private theorem scanActualTypes_failure_mem (bindings : Bindings)
    (expected : Atom) (actuals : List Atom) :
    ∀ {actual}, actual ∈ (scanActualTypes bindings expected actuals).failures →
      actual ∈ actuals := by
  induction actuals with
  | nil => simp [scanActualTypes]
  | cons head tail ih =>
      intro actual member
      simp only [scanActualTypes] at member
      split at member
      · exact List.mem_cons_of_mem head (ih member)
      · rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head (ih member)

/-- A nonempty scan with no selected match retains at least one failure. -/
private theorem scanActualTypes_failures_ne_nil_of_selected_none
    (bindings : Bindings) (expected : Atom) (head : Atom) (tail : List Atom)
    (selected : (scanActualTypes bindings expected (head :: tail)).selected = none) :
    (scanActualTypes bindings expected (head :: tail)).failures ≠ [] := by
  cases matchEq : matchType bindings expected head with
  | none => simp [scanActualTypes, matchEq]
  | some output => simp [scanActualTypes, matchEq] at selected

/-- The detailed checker never fabricates the first actual type in a rejected
argument block. -/
private theorem typeCheckArgsDetailedOutcomeScoped_first_act_real
    (env : MinEnv) (w : World)
    (argTypes : List Atom) (boundaryScope : List VarName) :
    ∀ (i : Nat) (tb : Bindings) (args : List Atom)
      (firstError : TypeCheckArgsError) (moreErrors : List TypeCheckArgsError),
    typeCheckArgsDetailedOutcomeScoped env w argTypes boundaryScope i tb args =
      .failure firstError moreErrors →
    ∃ arg ∈ args, ∃ raw ∈ getTypes env (typePrep w arg),
      TypeCandidateFresheningRel raw firstError.actual := by
  intro i tb args
  induction args generalizing i tb with
  | nil => intro firstError moreErrors h
           simp [typeCheckArgsDetailedOutcomeScoped] at h
  | cons ai more ih =>
      intro firstError moreErrors h
      simp only [typeCheckArgsDetailedOutcomeScoped] at h
      split at h
      · simp at h
      · rename_i formalOption formal formalEq
        split at h
        · split at h
          · simp at h
          · next laterFirst laterErrors recursiveEq =>
              cases h
              obtain ⟨arg, hmem, raw, hraw, observed⟩ :=
                ih (i + 1) _ firstError laterErrors recursiveEq
              exact ⟨arg, List.mem_cons_of_mem ai hmem, raw, hraw, observed⟩
        · next selectedNone =>
          split at h
          · next currentFirst currentRest currentErrorsEq =>
              cases h
              refine ⟨ai, List.mem_cons_self, ?_⟩
              have currentMember : firstError ∈
                  (scanActualTypes tb formal
                    ((getTypes env (typePrep w ai)).map
                      (freshenTypeCandidate
                        (boundaryScope ++ typeInferenceAvoid env (Atom.expr (ai :: more))
                          (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i))).failures.map
                    (fun actual =>
                      TypeCheckArgsError.mk (i + 1)
                        (instantiate tb formal) actual) := by
                rw [currentErrorsEq]
                exact List.mem_cons_self
              rcases List.mem_map.mp currentMember with
                ⟨observed, observedFailure, observedEq⟩
              have observedActual := scanActualTypes_failure_mem tb _ _ observedFailure
              rcases List.mem_map.mp observedActual with ⟨raw, rawMember, rawEq⟩
              refine ⟨raw, rawMember, ?_⟩
              refine ⟨boundaryScope ++ typeInferenceAvoid env (Atom.expr (ai :: more))
                  (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars, i, ?_⟩
              cases observedEq
              exact rawEq.symm
          · next currentErrorsEmpty =>
              obtain ⟨rawHead, rawTail, rawTypesEq⟩ :=
                List.exists_cons_of_ne_nil (getTypes_ne_nil env (typePrep w ai))
              have actualsNonempty :
                  (getTypes env (typePrep w ai)).map
                    (freshenTypeCandidate
                      (boundaryScope ++ typeInferenceAvoid env (Atom.expr (ai :: more))
                        (argTypes ++ getTypes env (typePrep w ai)) ++ tb.vars) i) ≠ [] := by
                rw [rawTypesEq]
                simp
              obtain ⟨actualHead, actualTail, actualsEq⟩ :=
                List.exists_cons_of_ne_nil actualsNonempty
              have failuresNonempty :=
                scanActualTypes_failures_ne_nil_of_selected_none tb formal
                  actualHead actualTail (by
                    rw [← actualsEq]
                    exact selectedNone)
              exfalso
              apply failuresNonempty
              rw [← actualsEq]
              cases failuresEq :
                  (scanActualTypes tb formal
                    ((getTypes env (typePrep w ai)).map
                      (freshenTypeCandidate
                        (boundaryScope ++ typeInferenceAvoid env
                          (Atom.expr (ai :: more))
                          (argTypes ++ getTypes env (typePrep w ai)) ++
                            tb.vars) i))).failures with
              | nil => rfl
              | cons failed failures =>
                  rw [failuresEq] at currentErrorsEmpty
                  simp at currentErrorsEmpty

/-- Ordinary detailed checking inherits the scoped no-fabrication theorem at
the complete source boundary. -/
private theorem typeCheckArgsDetailedOutcome_first_act_real
    (env : MinEnv) (w : World) (argTypes : List Atom) :
    ∀ (i : Nat) (tb : Bindings) (args : List Atom)
      (firstError : TypeCheckArgsError) (moreErrors : List TypeCheckArgsError),
    typeCheckArgsDetailedOutcome env w argTypes i tb args =
      .failure firstError moreErrors →
    ∃ arg ∈ args, ∃ raw ∈ getTypes env (typePrep w arg),
      TypeCandidateFresheningRel raw firstError.actual := by
  intro i tb args firstError moreErrors failure
  exact typeCheckArgsDetailedOutcomeScoped_first_act_real env w argTypes
    (applicationTypeInferenceScope (Atom.sym "%Undefined%") args)
    i tb args firstError moreErrors failure

/-- The compatibility checker projection never fabricates the first actual
type in a rejected argument. -/
private theorem typeCheckArgsOutcome_act_real (env : MinEnv) (w : World)
    (argTypes : List Atom) :
    ∀ (i : Nat) (tb : Bindings) (args : List Atom) (j : Nat) (e a : Atom),
    typeCheckArgsOutcome env w argTypes i tb args = .failure j e a →
    ∃ arg ∈ args, ∃ raw ∈ getTypes env (typePrep w arg),
      TypeCandidateFresheningRel raw a := by
  intro i tb args j e a h
  cases detailedEq :
      typeCheckArgsDetailedOutcome env w argTypes i tb args with
  | success bindings latentErrors =>
      simp [typeCheckArgsOutcome, detailedEq] at h
  | failure firstError moreErrors =>
      simp [typeCheckArgsOutcome, detailedEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact typeCheckArgsDetailedOutcome_first_act_real env w argTypes
        i tb args firstError moreErrors detailedEq

/-- **No fabricated type errors.** The *actual* type reported in a `BadArgType` is a
capture-avoiding freshening of a genuine raw type of the offending argument.  Thus the checker may
give private type variables new spellings, but it never invents a type candidate: combined with
`mettaEval_badArgType`, a `BadArgType (pos, expected, actual)` names a real parameter type and an
alpha-presented argument type. -/
theorem typeCheckArgs_act_real (env : MinEnv) (w : World) (argTypes : List Atom)
    (i : Nat) (tb : Bindings) (args : List Atom) (j : Nat) (e a : Atom)
    (h : typeCheckArgs env w argTypes i tb args = some (j, e, a)) :
    ∃ arg ∈ args, ∃ raw ∈ getTypes env (typePrep w arg),
      TypeCandidateFresheningRel raw a := by
  unfold typeCheckArgs at h
  generalize hout : typeCheckArgsOutcome env w argTypes i tb args = outcome at h
  cases outcome with
  | success bindings => simp at h
  | failure position expected actual =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact typeCheckArgsOutcome_act_real env w argTypes i tb args
        position expected actual hout

/-! ## Preservation for the grounded numeric core

The grounded operations **preserve types**: arithmetic is closed on numbers, and comparison /
equality yield Booleans (or propagate an error). Together with the gradual checker above, these
lemmas are the preservation half of type soundness for the grounded core. A well-typed `(+ …)`
always reduces to a `Number`, never a stuck or mistyped atom. -/

/-- **Arithmetic is closed on `Number`.** Any `numBin` (`+`, `-`, `*`) that returns a value returns a
numeric grounded atom, either an `Int` or a `Float`, never a symbol, variable, or expression. So a
well-typed arithmetic redex reduces to a `Number`: type is preserved. -/
theorem numBin_isNumber (fi : Int → Int → Int) (ff : Float → Float → Float)
    (args : List Atom) (r : Atom)
    (h : Builtins.numBin fi ff args = ReduceResult.ok [r]) :
    (∃ n : Int, r = Atom.gnd (Ground.int n)) ∨ (∃ x : Float, r = Atom.gnd (Ground.float x)) := by
  unfold Builtins.numBin at h
  split at h <;>
    simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true, reduceCtorEq] at h
  · exact Or.inl ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩
  · exact Or.inr ⟨_, h.symm⟩

/-- **Comparison yields `Bool`.** Any `numCmp` (`<`, `<=`, `>`, `>=`) that returns a value returns a
Boolean grounded atom. -/
theorem numCmp_isBool (fi : Int → Int → Bool) (ff : Float → Float → Bool)
    (args : List Atom) (r : Atom)
    (h : Builtins.numCmp fi ff args = ReduceResult.ok [r]) :
    ∃ b : Bool, r = Atom.gnd (Ground.bool b) := by
  unfold Builtins.numCmp at h
  split at h <;>
    simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true, reduceCtorEq] at h
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩

/-- **Equality yields `Bool`, or propagates an error.** `==` returns a Boolean grounded atom, unless
one argument is itself an `(Error …)`, which it lifts unchanged (Hyperon's error-propagating `==`).
So `==` never produces a mistyped result: it is a `Bool` or a faithfully-propagated error. -/
theorem eqAtom_isBoolOrError (args : List Atom) (r : Atom)
    (h : Builtins.eqAtom args = ReduceResult.ok [r]) :
    (∃ b : Bool, r = Atom.gnd (Ground.bool b)) ∨ r.isError = true := by
  unfold Builtins.eqAtom at h
  split at h
  · rename_i a b
    split at h
    · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
      exact Or.inr (by rw [← h]; assumption)
    · split at h
      · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
        exact Or.inr (by rw [← h]; assumption)
      · simp only [ReduceResult.ok.injEq, List.cons.injEq, and_true] at h
        exact Or.inl ⟨_, h.symm⟩
  · simp only [reduceCtorEq] at h

end Metta
