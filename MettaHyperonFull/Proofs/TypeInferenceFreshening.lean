import MettaHyperonFull.Proofs.CaptureAvoidingFreshening

/-!
# Capture-avoiding type-inference candidates

Type annotations use source-level variable spellings, while application type
inference combines candidates from independently declared annotations.  Each
candidate is therefore renamed at the inference boundary.  Argument
candidates grow the finite avoid set from left to right, and function
candidates avoid every generated argument name.

These laws pin the repair independently of the evaluator: selected candidates
remain alpha-renamings of their annotations, contain no initially forbidden
name, and cannot share a private variable with the argument candidates against
which they are matched.
-/

namespace Metta.Minimal
open Metta

/-! ## Positional separation of private type scopes -/

/-- The decimal counter printed at the end of a private fresh name contains
no separator character. -/
theorem nat_toString_hash_not_mem (counter : Nat) :
    '#' ∉ (toString counter).toList := by
  intro member
  have digit := Nat.isDigit_of_mem_toDigits
    (b := 10) (n := counter) (c := '#') (by decide) (by decide)
  rw [show (toString counter).toList = Nat.toDigits 10 counter by
    exact Nat.toList_repr (n := counter)] at member
  have := digit member
  have hashNotDigit : '#'.isDigit = false := by decide
  rw [hashNotDigit] at this
  contradiction

/-- Characters after the last `#`; the private freshener's terminal counter
is recovered through this executable-independent observation. -/
private def suffixAfterLastHash (name : String) : List Char :=
  (name.toList.splitOn '#').getLast?.getD []

private theorem suffixAfterLastHash_append_counter
    (base digits : String) (hashFree : '#' ∉ digits.toList) :
    suffixAfterLastHash (base ++ "#" ++ digits) = digits.toList := by
  unfold suffixAfterLastHash
  rw [String.toList_append, String.toList_append]
  change (((base.toList ++ ['#']) ++ digits.toList).splitOn '#').getLast?.getD [] =
    digits.toList
  rw [List.append_assoc]
  change ((base.toList ++ '#' :: digits.toList).splitOn '#').getLast?.getD [] =
    digits.toList
  rw [List.splitOn_append_cons_self,
    List.splitOn_eq_singleton hashFree]
  simp

/-- Fresh names made at distinct positional counters cannot collide, even
when their avoid sets and source spellings are unrelated. -/
theorem captureAvoidingName_ne_of_counter_ne
    {leftAvoid rightAvoid : List VarName}
    {leftCounter rightCounter : Nat} {left right : VarName}
    (counterNe : leftCounter ≠ rightCounter) :
    captureAvoidingName leftAvoid leftCounter left ≠
      captureAvoidingName rightAvoid rightCounter right := by
  intro equal
  have suffixEqual := congrArg suffixAfterLastHash equal
  have leftSuffix := suffixAfterLastHash_append_counter
    (avoidancePrefix leftAvoid ++ left) (toString leftCounter)
      (nat_toString_hash_not_mem leftCounter)
  have rightSuffix := suffixAfterLastHash_append_counter
    (avoidancePrefix rightAvoid ++ right) (toString rightCounter)
      (nat_toString_hash_not_mem rightCounter)
  rw [show captureAvoidingName leftAvoid leftCounter left =
      (avoidancePrefix leftAvoid ++ left) ++ "#" ++
        toString leftCounter by
        simp [captureAvoidingName, String.append_assoc],
    show captureAvoidingName rightAvoid rightCounter right =
      (avoidancePrefix rightAvoid ++ right) ++ "#" ++
        toString rightCounter by
        simp [captureAvoidingName, String.append_assoc]] at suffixEqual
  rw [leftSuffix, rightSuffix] at suffixEqual
  apply counterNe
  exact Nat.repr_injective
    (String.toList_injective suffixEqual)

mutual

/-- Whole-atom freshening maps the variable-occurrence list pointwise. -/
theorem vars_renameAllVars (rename : VarName → VarName) (atom : Atom) :
    (renameAllVars rename atom).vars = atom.vars.map rename := by
  cases atom with
  | sym name => simp [renameAllVars, Atom.vars]
  | var name => simp [renameAllVars, Atom.vars]
  | gnd value => simp [renameAllVars, Atom.vars]
  | expr atoms =>
      simpa [renameAllVars, Atom.vars] using
        varsList_renameAllVars rename atoms

/-- List companion of `vars_renameAllVars`. -/
theorem varsList_renameAllVars
    (rename : VarName → VarName) (atoms : List Atom) :
    ((atoms.map (renameAllVars rename)).map Atom.vars).flatten =
      ((atoms.map Atom.vars).flatten).map rename := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.flatten_cons, List.map_append]
      exact congrArg₂ List.append
        (vars_renameAllVars rename atom)
        (varsList_renameAllVars rename atoms)

end

/-- Every variable occurrence in one fresh type records that candidate's
single positional counter. -/
theorem freshenTypeCandidate_var_generated
    (avoid : List VarName) (position : Nat) (type : Atom) :
    ∀ name ∈ (freshenTypeCandidate avoid position type).vars,
      ∃ source ∈ type.vars,
        name = captureAvoidingName avoid position source := by
  intro name member
  simp only [freshenTypeCandidate, vars_renameAllVars] at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact ⟨source, sourceMember, rfl⟩

/-- Every variable generated by the argument fold has a counter strictly
below the first position after that fold. -/
theorem freshenArgumentTypes_var_counter_lt
    (avoid : List VarName) (position : Nat) (types : List Atom) :
    ∀ name ∈ (freshenArgumentTypes avoid position types).flatMap Atom.vars,
      ∃ generatedAvoid counter source,
        counter < position + types.length ∧
        name = captureAvoidingName generatedAvoid counter source := by
  induction types generalizing avoid position with
  | nil => simp [freshenArgumentTypes]
  | cons type types ih =>
      intro name member
      simp only [freshenArgumentTypes, List.flatMap_cons,
        List.mem_append] at member
      rcases member with headMember | tailMember
      · obtain ⟨source, _sourceMember, equation⟩ :=
          freshenTypeCandidate_var_generated avoid position type
            name headMember
        exact ⟨avoid, position, source, by simp, equation⟩
      · let fresh := freshenTypeCandidate avoid position type
        obtain ⟨generatedAvoid, counter, source, bound, equation⟩ :=
          ih (avoid ++ fresh.vars) (position + 1) name tailMember
        refine ⟨generatedAvoid, counter, source, ?_, equation⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bound

/-- Function position `types.length` is disjoint from every argument
position `0 .. types.length - 1`, independently of avoid sets and source
variable spellings.  This is the cross-family scope law used by the repaired
Cartesian type inference. -/
theorem freshenTypeCandidate_disjoint_from_positioned_arguments
    (argumentAvoid functionAvoid : List VarName)
    (functionType : Atom) (argumentTypes : List Atom) :
    ∀ name ∈
        (freshenTypeCandidate functionAvoid argumentTypes.length
          functionType).vars,
      name ∉
        (freshenArgumentTypes argumentAvoid 0 argumentTypes).flatMap
          Atom.vars := by
  intro name functionMember argumentMember
  obtain ⟨functionSource, _functionSourceMember, functionEquation⟩ :=
    freshenTypeCandidate_var_generated functionAvoid argumentTypes.length
      functionType name functionMember
  obtain ⟨generatedAvoid, counter, argumentSource, counterBound,
      argumentEquation⟩ :=
    freshenArgumentTypes_var_counter_lt argumentAvoid 0 argumentTypes
      name argumentMember
  have counterNe : counter ≠ argumentTypes.length := by omega
  exact captureAvoidingName_ne_of_counter_ne counterNe
    (argumentEquation.symm.trans functionEquation)

/-- Every variable generated for one type candidate is outside its finite
avoid set. -/
theorem freshenTypeCandidate_vars_fresh
    (avoid : List VarName) (position : Nat) (type : Atom) :
    ∀ name ∈ (freshenTypeCandidate avoid position type).vars,
      name ∉ avoid := by
  exact renameAllVars_avoids avoid (captureAvoidingName avoid position)
    (captureAvoidingName_not_mem avoid position) type

/-- Every private variable in every expected-selection signature avoids the
complete live/public selection scope used to create the presentation. -/
theorem freshenFunctionTypeCandidatesAvoiding_vars_fresh
    (env : MinEnv) (expression : Atom) (args : List Atom) (expected : Atom)
    (liveAvoid : List VarName) (rawCandidates : List Atom) :
    ∀ candidate ∈ freshenFunctionTypeCandidatesAvoiding env expression args
        expected liveAvoid rawCandidates,
      ∀ name ∈ candidate.vars,
        name ∉ functionTypeSelectionAvoiding env expression args expected
          liveAvoid rawCandidates := by
  intro candidate candidateMember name nameMember
  simp only [freshenFunctionTypeCandidatesAvoiding, List.mem_map] at candidateMember
  obtain ⟨rawCandidate, rawMember, rfl⟩ := candidateMember
  exact freshenTypeCandidate_vars_fresh
    (functionTypeSelectionAvoiding env expression args expected liveAvoid
      rawCandidates) args.length rawCandidate name nameMember

/-- In particular, private expected-selection signature variables cannot
reuse a spelling from the live evaluator binding. -/
theorem freshenFunctionTypeCandidatesAvoiding_vars_avoid_live
    (env : MinEnv) (expression : Atom) (args : List Atom) (expected : Atom)
    (liveAvoid : List VarName) (rawCandidates : List Atom) :
    ∀ candidate ∈ freshenFunctionTypeCandidatesAvoiding env expression args
        expected liveAvoid rawCandidates,
      ∀ name ∈ candidate.vars, name ∉ liveAvoid := by
  intro candidate candidateMember name nameMember liveMember
  have fresh := freshenFunctionTypeCandidatesAvoiding_vars_fresh env
    expression args expected liveAvoid rawCandidates candidate candidateMember
    name nameMember
  exact fresh (List.mem_append_left _ liveMember)

/-- All argument-candidate variables remain outside the avoid set supplied at
the beginning of the fold. -/
theorem freshenArgumentTypes_vars_fresh
    (avoid : List VarName) (position : Nat) (types : List Atom) :
    ∀ name ∈ (freshenArgumentTypes avoid position types).flatMap Atom.vars,
      name ∉ avoid := by
  induction types generalizing avoid position with
  | nil =>
      simp [freshenArgumentTypes]
  | cons type types ih =>
      let fresh := freshenTypeCandidate avoid position type
      intro name hmem
      simp only [freshenArgumentTypes, List.flatMap_cons,
        List.mem_append] at hmem
      rcases hmem with hhere | hrest
      · exact freshenTypeCandidate_vars_fresh avoid position type name hhere
      · have hnot := ih (avoid ++ fresh.vars) (position + 1) name hrest
        intro havoid
        exact hnot (List.mem_append_left _ havoid)

/-- A function candidate freshened against the generated argument candidates
cannot share a private variable spelling with any of them. -/
theorem freshenTypeCandidate_disjoint_from_arguments
    (avoid : List VarName) (functionPosition : Nat)
    (functionType : Atom) (argumentTypes : List Atom) :
    let freshArguments := freshenArgumentTypes avoid 0 argumentTypes
    ∀ name ∈ (freshenTypeCandidate
        (avoid ++ freshArguments.flatMap Atom.vars)
        functionPosition functionType).vars,
      name ∉ freshArguments.flatMap Atom.vars := by
  intro freshArguments name hname harguments
  have hfresh := freshenTypeCandidate_vars_fresh
    (avoid ++ freshArguments.flatMap Atom.vars)
    functionPosition functionType name hname
  exact hfresh (List.mem_append_right _ harguments)

private def repeatedAnnotationArguments : List Atom :=
  freshenArgumentTypes ["t"] 0 [.var "t", .var "t"]

/-- Capability canary: two independent argument annotations using the same
source spelling receive distinct private names. -/
theorem repeated_annotation_variables_are_distinct :
    ∃ first second,
      repeatedAnnotationArguments = [.var first, .var second] ∧
        first ≠ second := by
  let first := captureAvoidingName ["t"] 0 "t"
  let second := captureAvoidingName (["t"] ++ [first]) 1 "t"
  refine ⟨first, second, ?_, ?_⟩
  · simp [repeatedAnnotationArguments, freshenArgumentTypes,
      freshenTypeCandidate, renameAllVars, Atom.vars, first, second]
  · intro heq
    have hfresh := captureAvoidingName_not_mem (["t"] ++ [first]) 1 "t"
    apply hfresh
    have heq' : captureAvoidingName (["t"] ++ [first]) 1 "t" = first := by
      simpa [second] using heq.symm
    rw [heq']
    simp

end Metta.Minimal
