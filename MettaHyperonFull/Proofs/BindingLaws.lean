-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.BindingLaws
Layer: Proofs
Purpose: Executable laws for equality-class-aware binding merge, resolution, and instantiation.
  The laws cover fresh values, explicit aliases, retained reconciliation constraints, connected
  nonlinear classes, incompatible class values, compound resolution, and cycle rejection.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none
Main exports: Bindings.lookupVal_empty, Bindings.lookupVal_addValRaw_self,
  Bindings.addVarBinding_var, Bindings.addVarBinding_fresh,
  Bindings.addVarBinding_nochange, Bindings.addVarBinding_reconciles,
  Bindings.addVarBinding_secondaryConflict, Bindings.addVarBinding_conflict,
  Bindings.seededOverwrite_reconciliation_rejected,
  Bindings.addVarEquality_nochange, Bindings.addVarEquality_reconciles,
  Bindings.addVarEquality_secondaryConflict, Bindings.addVarEquality_conflict,
  Bindings.merge_empty_right, matchAtoms_var_var_equality,
  Unify.varBinding_mem_or_mem_aliasTrace_of_unifyRounds,
  Unify.varBinding_mem_aliasTrace_of_unifyRounds_empty,
  connectedClass_match, connectedClass_instantiation, connectedClass_bindingReadout,
  incompatibleClassValues_rejected, compoundClassValue_resolves, compoundCycle_hasLoop
Open obligations: semantic permutation invariance and the general matcher transport theorem live at
  the representation-independent conformance layer.
-/
import MettaHyperonFull.Proofs.Basic

namespace Metta

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Bindings

/-- Looking up any value in the empty binding set fails. -/
theorem lookupVal_empty (x : VarName) : lookupVal [] x = none := rfl

/-- Raw value insertion makes the inserted value immediately visible at that variable. -/
theorem lookupVal_addValRaw_self (b : Bindings) (x : VarName) (v : Atom) :
    lookupVal (addValRaw b x v) x = some v := by
  simp [addValRaw, lookupVal]

theorem classValues_eq_nil_of_lookupVal_none {b : Bindings}
    (hlookup : ∀ x, lookupVal b x = none) (x : VarName) :
    classValues b x = [] := by
  simp [classValues, hlookup]

/-- POSITIVE: permuting normalized direct-value relations does not change the
    canonical value view of an equality class. -/
theorem classValues_value_relation_permutation :
    classValues
        [BindingRel.val "y" (Atom.sym "B"),
          BindingRel.eq "y" "x",
          BindingRel.val "x" (Atom.sym "A")]
        "x" =
      classValues
        [BindingRel.val "x" (Atom.sym "A"),
          BindingRel.eq "y" "x",
          BindingRel.val "y" (Atom.sym "B")]
        "x" := by
  rfl

/-- NEGATIVE: duplicate direct values for one key are not normalized; direct
    lookup deliberately exposes their order instead of pretending the malformed
    inputs are equivalent binding sets. -/
theorem classValues_duplicate_key_order_visible :
    classValues
        [BindingRel.val "x" (Atom.sym "A"),
          BindingRel.val "x" (Atom.sym "B")]
        "x" ≠
      classValues
        [BindingRel.val "x" (Atom.sym "B"),
          BindingRel.val "x" (Atom.sym "A")]
        "x" := by
  simp [classValues, eqClassOrdered, eqVarsInOrder, eqClass, eqClassAux,
    eqStep, lookupVal]

/-- A variable-valued binding is represented as an explicit equality. -/
theorem addVarBinding_var (b : Bindings) (x y : VarName) :
    addVarBinding b x (Atom.var y) = addVarEquality b x y := rfl

/-- A fresh non-variable value extends the binding set. -/
theorem addVarBinding_fresh {b : Bindings} {x : VarName} {v : Atom}
    (hclass : classValues b x = [])
    (hnotvar : ∀ y, v ≠ Atom.var y) :
    addVarBinding b x v = [addValRaw b x v] := by
  cases v <;> simp_all [addVarBinding]

/-- A class-local reconciliation that requires no substitution leaves the
    existing binding presentation unchanged. -/
theorem addVarBinding_nochange {b : Bindings} {x : VarName} {v : Atom}
    {values : List Atom}
    (hnotvar : ∀ y, v ≠ Atom.var y)
    (hvalues : classValues b x = values)
    (hvaluesNonempty : values ≠ [])
    (hunify : unifyValues (values ++ [v]) = some []) :
    addVarBinding b x v = [b] := by
  cases values with
  | nil => contradiction
  | cons value values => cases v <;> simp_all [addVarBinding]

/-- A nontrivial class-local reconciliation is accepted only after the same
    constraint is reconciled against the complete seeded binding set. -/
theorem addVarBinding_reconciles {b : Bindings} {x : VarName} {v : Atom}
    {values : List Atom} {localHead : VarName × Atom} {localTail sigma : Subst}
    (hnotvar : ∀ y, v ≠ Atom.var y)
    (hvalues : classValues b x = values)
    (hvaluesNonempty : values ≠ [])
    (hunify : unifyValues (values ++ [v]) = some (localHead :: localTail))
    (hall : reconcileAll b [(Atom.var x, v)] = some sigma) :
    addVarBinding b x v =
      [rebuildFromReconciliation b b [(Atom.var x, v)] sigma] := by
  cases values with
  | nil => contradiction
  | cons value values => cases v <;> simp_all [addVarBinding]

/-- A locally compatible value is rejected when its internal substitution
    conflicts with a seeded binding elsewhere in the complete equation set. -/
theorem addVarBinding_secondaryConflict
    {b : Bindings} {x : VarName} {v : Atom}
    {values : List Atom} {localHead : VarName × Atom} {localTail : Subst}
    (hnotvar : ∀ y, v ≠ Atom.var y)
    (hvalues : classValues b x = values)
    (hvaluesNonempty : values ≠ [])
    (hunify : unifyValues (values ++ [v]) = some (localHead :: localTail))
    (hall : reconcileAll b [(Atom.var x, v)] = none) :
    addVarBinding b x v = [] := by
  cases values with
  | nil => contradiction
  | cons value values => cases v <;> simp_all [addVarBinding]

/-- An incompatible non-variable value is rejected class-wide. -/
theorem addVarBinding_conflict {b : Bindings} {x : VarName} {v : Atom}
    {values : List Atom}
    (hnotvar : ∀ y, v ≠ Atom.var y)
    (hvalues : classValues b x = values)
    (hvaluesNonempty : values ≠ [])
    (hunify : unifyValues (values ++ [v]) = none) :
    addVarBinding b x v = [] := by
  cases v <;> simp_all [addVarBinding]

/-- NEGATIVE: complete reconciliation rejects a class-local substitution that
    would overwrite an existing seeded value through an internal variable. -/
theorem seededOverwrite_reconciliation_rejected :
    addVarBinding
        [BindingRel.val "p" (.expr [.sym "f", .var "a"]),
          BindingRel.val "a" (.sym "old")]
        "p" (.expr [.sym "f", .sym "new"]) = [] := by
  simp (config := { maxSteps := 1000000 })
    [addVarBinding, unifyValues, reconcileAll, equations,
      relationEquation, equationFuel, classValues, eqClassOrdered,
      eqVarsInOrder, eqClass, eqClassAux, eqStep, lookupVal,
      Unify.unifyRounds, Unify.decomposeAll, Unify.decomposeEq,
      Unify.decomposeList, Subst.occurs, Subst.apply, Subst.lookup, Subst.extend,
      Subst.erase, Atom.size]

/-- A joined class requiring no substitution retains the explicit new alias. -/
theorem addVarEquality_nochange {b : Bindings} {x y : VarName}
    (h : unifyValues (classValues (addEqRaw b x y) x) = some []) :
    addVarEquality b x y = [addEqRaw b x y] := by
  simp [addVarEquality, h]

/-- Nontrivial equality-class reconciliation is replayed only after checking
    the complete seeded equation system. -/
theorem addVarEquality_reconciles
    {b : Bindings} {x y : VarName}
    {localHead : VarName × Atom} {localTail sigma : Subst}
    (hlocal :
      unifyValues (classValues (addEqRaw b x y) x) =
        some (localHead :: localTail))
    (hall : reconcileAll b [(Atom.var x, Atom.var y)] = some sigma) :
    addVarEquality b x y =
      [rebuildFromReconciliation (addEqRaw b x y) b
        [(Atom.var x, Atom.var y)] sigma] := by
  simp [addVarEquality, hlocal, hall]

/-- A locally compatible joined class is rejected when it conflicts with a
    seeded binding elsewhere. -/
theorem addVarEquality_secondaryConflict
    {b : Bindings} {x y : VarName}
    {localHead : VarName × Atom} {localTail : Subst}
    (hlocal :
      unifyValues (classValues (addEqRaw b x y) x) =
        some (localHead :: localTail))
    (hall : reconcileAll b [(Atom.var x, Atom.var y)] = none) :
    addVarEquality b x y = [] := by
  simp [addVarEquality, hlocal, hall]

/-- Equality classes whose values cannot unify are rejected. -/
theorem addVarEquality_conflict {b : Bindings} {x y : VarName}
    (h : unifyValues (classValues (addEqRaw b x y) x) = none) :
    addVarEquality b x y = [] := by
  simp [addVarEquality, h]

/-- Merging an empty right-hand binding set is the identity singleton. -/
theorem merge_empty_right (b : Bindings) : merge b [] = [b] := rfl

end Bindings

/-- Decomposing two variable-free atoms can produce no variable constraints. -/
theorem Unify.decomposeEq_some_eq_nil_of_closed :
    ∀ (left right : Atom) (constraints : List (VarName × Atom)),
      left.vars = [] → right.vars = [] →
        Unify.decomposeEq left right = some constraints → constraints = [] := by
  intro left
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol right constraints _ hright hdecomp
    cases right with
    | var v => simp [Atom.vars] at hright
    | sym other =>
        simp [Unify.decomposeEq] at hdecomp
        exact hdecomp.2
    | gnd g => simp [Unify.decomposeEq] at hdecomp
    | expr xs => simp [Unify.decomposeEq] at hdecomp
  · intro v right constraints hleft _ _
    simp [Atom.vars] at hleft
  · intro g right constraints _ hright hdecomp
    cases right with
    | var v => simp [Atom.vars] at hright
    | sym symbol => simp [Unify.decomposeEq] at hdecomp
    | gnd other =>
        simp [Unify.decomposeEq] at hdecomp
        exact hdecomp.2
    | expr xs => simp [Unify.decomposeEq] at hdecomp
  · intro xs ih right constraints hleft hright hdecomp
    cases right with
    | var v => simp [Atom.vars] at hright
    | sym symbol => simp [Unify.decomposeEq] at hdecomp
    | gnd ground => simp [Unify.decomposeEq] at hdecomp
    | expr ys =>
        have hxsClosed : ∀ child ∈ xs, child.vars = [] := by
          intro child hchild
          simp only [Atom.vars] at hleft
          rw [List.flatten_eq_nil_iff] at hleft
          exact hleft child.vars (List.mem_map_of_mem hchild)
        have hysClosed : ∀ child ∈ ys, child.vars = [] := by
          intro child hchild
          simp only [Atom.vars] at hright
          rw [List.flatten_eq_nil_iff] at hright
          exact hright child.vars (List.mem_map_of_mem hchild)
        have hlist : ∀ (lefts rights : List Atom) constraints,
            (∀ child ∈ lefts, child ∈ xs) →
            (∀ child ∈ rights, child.vars = []) →
            Unify.decomposeList lefts rights = some constraints → constraints = [] := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights constraints _ _ h
              cases rights <;> simp [Unify.decomposeList] at h ⊢
              exact h
          | cons head tail ihTail =>
              intro rights constraints hsubset hrights h
              cases rights with
              | nil => simp [Unify.decomposeList] at h
              | cons rightHead rightTail =>
                  cases hhead : Unify.decomposeEq head rightHead with
                  | none => simp [Unify.decomposeList, hhead] at h
                  | some headConstraints =>
                      cases htail : Unify.decomposeList tail rightTail with
                      | none => simp [Unify.decomposeList, hhead, htail] at h
                      | some tailConstraints =>
                          simp [Unify.decomposeList, hhead, htail] at h
                          have hheadNil : headConstraints = [] :=
                            ih head (hsubset head (by simp)) rightHead headConstraints
                              (hxsClosed head (hsubset head (by simp)))
                              (hrights rightHead (by simp)) hhead
                          have htailNil : tailConstraints = [] :=
                            ihTail rightTail tailConstraints
                              (fun child hchild => hsubset child (by simp [hchild]))
                              (fun child hchild => hrights child (by simp [hchild])) htail
                          subst headConstraints
                          subst tailConstraints
                          simpa using h
        exact hlist xs ys constraints (fun child hchild => hchild) hysClosed hdecomp

/-- Decomposing a variable-free equation worklist can produce no variable constraints. -/
theorem Unify.decomposeAll_some_eq_nil_of_closed :
    ∀ (equations : List (Atom × Atom)) (constraints : List (VarName × Atom)),
      (∀ equation ∈ equations, equation.1.vars = [] ∧ equation.2.vars = []) →
      Unify.decomposeAll equations = some constraints → constraints = [] := by
  intro equations
  induction equations with
  | nil => intro constraints _ h; simpa [Unify.decomposeAll] using h
  | cons equation rest ih =>
      intro constraints hclosed hdecomp
      cases hhead : Unify.decomposeEq equation.1 equation.2 with
      | none => simp [Unify.decomposeAll, hhead] at hdecomp
      | some headConstraints =>
          cases htail : Unify.decomposeAll rest with
          | none => simp [Unify.decomposeAll, hhead, htail] at hdecomp
          | some tailConstraints =>
              simp [Unify.decomposeAll, hhead, htail] at hdecomp
              have heqClosed := hclosed equation (by simp)
              have hheadNil := Unify.decomposeEq_some_eq_nil_of_closed equation.1 equation.2
                headConstraints heqClosed.1 heqClosed.2 hhead
              have htailNil := ih tailConstraints
                (fun item hitem => hclosed item (by simp [hitem])) htail
              subst headConstraints
              subst tailConstraints
              simpa using hdecomp

/-- Running unification on a variable-free equation worklist preserves the incoming substitution. -/
theorem Unify.unifyRounds_some_eq_of_closed (fuel : Nat) (equations : List (Atom × Atom))
    (subst result : Subst)
    (hclosed : ∀ equation ∈ equations, equation.1.vars = [] ∧ equation.2.vars = [])
    (hresult : Unify.unifyRounds fuel equations subst = some result) :
    result = subst := by
  cases hdecomp : Unify.decomposeAll equations with
  | none =>
      cases fuel <;> simp [Unify.unifyRounds, hdecomp] at hresult
  | some constraints =>
      have hnil := Unify.decomposeAll_some_eq_nil_of_closed equations constraints hclosed hdecomp
      subst constraints
      cases fuel <;> simpa [Unify.unifyRounds, hdecomp] using hresult.symm

/-- Successful reconciliation of variable-free values returns the empty substitution. -/
theorem Bindings.unifyValues_some_eq_empty_of_closed {values : List Atom} {result : Subst}
    (hclosed : ∀ value ∈ values, value.vars = [])
    (hresult : Bindings.unifyValues values = some result) : result = [] := by
  cases values with
  | nil => simpa [Bindings.unifyValues] using hresult.symm
  | cons first rest =>
      cases rest with
      | nil => simpa [Bindings.unifyValues] using hresult.symm
      | cons second tail =>
          apply Unify.unifyRounds_some_eq_of_closed
            (first.size + ((second :: tail).map Atom.size).sum)
            ((second :: tail).map fun value => (first, value)) [] result
          · intro equation hequation
            rcases List.mem_map.mp hequation with ⟨value, hvalue, rfl⟩
            exact ⟨hclosed first (by simp), hclosed value (by simp [hvalue])⟩
          · simpa [Bindings.unifyValues] using hresult

/-- Every variable-valued entry in a successful Robinson result is either an
incoming substitution entry or was exposed as an explicit variable/variable
constraint in the alias trace.  This is the first half of the reconciliation
trace-completeness dichotomy. -/
theorem Unify.varBinding_mem_or_mem_aliasTrace_of_unifyRounds
    {fuel : Nat} {equations : List (Atom × Atom)}
    {subst result : Subst} {x y : VarName}
    (hrun : Unify.unifyRounds fuel equations subst = some result)
    (hmem : (x, Atom.var y) ∈ result) :
    (x, Atom.var y) ∈ subst ∨ (x, y) ∈ Unify.aliasTrace fuel equations := by
  induction fuel generalizing equations subst result x y with
  | zero =>
      cases hdecomp : Unify.decomposeAll equations with
      | none => simp [Unify.unifyRounds, hdecomp] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Unify.unifyRounds, hdecomp] at hrun
              subst result
              exact Or.inl hmem
          | cons constraint rest =>
              simp [Unify.unifyRounds, hdecomp] at hrun
  | succ fuel ih =>
      cases hdecomp : Unify.decomposeAll equations with
      | none => simp [Unify.unifyRounds, hdecomp] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Unify.unifyRounds, hdecomp] at hrun
              subst result
              exact Or.inl hmem
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Subst.occurs key term with
              | true =>
                  simp [Unify.unifyRounds, hdecomp, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Subst.apply [(key, term)] (Atom.var item.1),
                      Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Unify.unifyRounds fuel remaining
                          (Subst.extend subst key term) = some result := by
                    simpa [Unify.unifyRounds, hdecomp, hoccurs,
                      remaining] using hrun
                  rcases ih hrun' hmem with hextended | htail
                  · simp only [Subst.extend, List.mem_cons] at hextended
                    rcases hextended with hhead | hold
                    · have hx : x = key := congrArg Prod.fst hhead
                      have hterm : Atom.var y = term := congrArg Prod.snd hhead
                      subst key
                      subst term
                      exact Or.inr (by
                        simp [Unify.aliasTrace, hdecomp, hoccurs,
                          Unify.aliasConstraints])
                    · exact Or.inl (List.mem_filter.mp hold).1
                  · exact Or.inr (by
                      simp [Unify.aliasTrace, hdecomp, hoccurs,
                        remaining, htail])

/-- With the empty incoming substitution used by whole-system
reconciliation, every variable-valued result entry belongs to the alias
trace. -/
theorem Unify.varBinding_mem_aliasTrace_of_unifyRounds_empty
    {fuel : Nat} {equations : List (Atom × Atom)}
    {result : Subst} {x y : VarName}
    (hrun : Unify.unifyRounds fuel equations [] = some result)
    (hmem : (x, Atom.var y) ∈ result) :
    (x, y) ∈ Unify.aliasTrace fuel equations := by
  rcases Unify.varBinding_mem_or_mem_aliasTrace_of_unifyRounds
      hrun hmem with h | h
  · simp at h
  · exact h

/-- Matching two distinct variables emits an explicit equality relation. -/
theorem matchAtoms_var_var_equality {x y : VarName} (h : (x == y) = false) :
    matchAtoms (Atom.var x) (Atom.var y) = [[BindingRel.eq x y]] := by
  simp [matchAtoms, matchAtomsWith, h]

def connectedClassPattern : Atom :=
  Atom.expr [Atom.sym "g", Atom.var "p1", Atom.var "p2", Atom.var "p2"]

def connectedClassQuery : Atom :=
  Atom.expr [Atom.sym "g", Atom.var "q1", Atom.var "q1", Atom.var "q2"]

def connectedClassBindings : Bindings :=
  [BindingRel.eq "p2" "q2", BindingRel.eq "p2" "q1", BindingRel.eq "p1" "q1"]

/-- POSITIVE: nonlinear matching preserves all three equality edges. -/
theorem connectedClass_match :
    matchAtoms connectedClassPattern connectedClassQuery = [connectedClassBindings] := by
  rfl

/-- POSITIVE: both RHS variables instantiate to one shared representative. -/
theorem connectedClass_instantiation :
    instantiate connectedClassBindings
      (Atom.expr [Atom.sym "f", Atom.var "p1", Atom.var "p2"]) =
      Atom.expr [Atom.sym "f", Atom.var "q1", Atom.var "q1"] := by
  change instantiate
      [BindingRel.eq "p2" "q2", BindingRel.eq "p2" "q1",
        BindingRel.eq "p1" "q1"]
      (Atom.expr [Atom.sym "f", Atom.var "p1", Atom.var "p2"]) = _
  have hlookup : ∀ x, Bindings.lookupVal
      [BindingRel.eq "p2" "q2", BindingRel.eq "p2" "q1",
        BindingRel.eq "p1" "q1"] x = none := by
    intro x
    simp [Bindings.lookupVal]
  have hclass := Bindings.classValues_eq_nil_of_lookupVal_none hlookup
  simp [instantiate, Bindings.resolveAtom,
    Bindings.resolve, Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, hclass, Bindings.eqRepresentative,
    Bindings.eqClassOrdered, Bindings.eqClass, Bindings.eqClassAux,
    Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size]

/-- POSITIVE: the minimal binding readout observes one equality class. -/
theorem connectedClass_bindingReadout :
    instantiate connectedClassBindings
      (Atom.expr [Atom.var "q1", Atom.var "q2"]) =
      Atom.expr [Atom.var "q1", Atom.var "q1"] := by
  change instantiate
      [BindingRel.eq "p2" "q2", BindingRel.eq "p2" "q1",
        BindingRel.eq "p1" "q1"]
      (Atom.expr [Atom.var "q1", Atom.var "q2"]) = _
  have hlookup : ∀ x, Bindings.lookupVal
      [BindingRel.eq "p2" "q2", BindingRel.eq "p2" "q1",
        BindingRel.eq "p1" "q1"] x = none := by
    intro x
    simp [Bindings.lookupVal]
  have hclass := Bindings.classValues_eq_nil_of_lookupVal_none hlookup
  simp [instantiate, Bindings.resolveAtom,
    Bindings.resolve, Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, hclass, Bindings.eqRepresentative,
    Bindings.eqClassOrdered, Bindings.eqClass, Bindings.eqClassAux,
    Bindings.eqStep, Bindings.eqVarsInOrder, Atom.size]

/-- NEGATIVE: equating classes with incompatible ground values is rejected. -/
theorem incompatibleClassValues_rejected :
    Bindings.addVarEquality
      [BindingRel.val "x" (Atom.sym "A"), BindingRel.val "y" (Atom.sym "B")]
      "x" "y" = [] := by
  have hclass :
      Bindings.classValues
          [BindingRel.eq "x" "y", BindingRel.val "x" (Atom.sym "A"),
            BindingRel.val "y" (Atom.sym "B")]
          "x" = [Atom.sym "B", Atom.sym "A"] := by
    rfl
  simp [Bindings.addVarEquality, Bindings.addEqRaw, hclass,
    Bindings.unifyValues, Unify.unifyRounds, Unify.decomposeAll,
    Unify.decomposeEq, Atom.size]

/-- POSITIVE: resolution descends through variables nested in compound values. -/
theorem compoundClassValue_resolves :
    instantiate
      [BindingRel.val "x" (Atom.expr [Atom.sym "f", Atom.var "y"]),
        BindingRel.val "y" (Atom.sym "A")]
      (Atom.var "x") = Atom.expr [Atom.sym "f", Atom.sym "A"] := by
  have hclass := Bindings.classValues_eq_lookupVal_toList_of_eqVarsInOrder_nil
    (b := [BindingRel.val "x" (Atom.expr [Atom.sym "f", Atom.var "y"]),
      BindingRel.val "y" (Atom.sym "A")]) (by rfl)
  simp [instantiate, Bindings.resolveAtom, Bindings.resolveAtomAux,
    Bindings.resolve, Bindings.resolutionFuel, Bindings.relationResolutionFuel,
    hclass, Bindings.lookupVal, Bindings.eqRepresentative,
    Bindings.eqClassOrdered, Bindings.eqVarsInOrder, Atom.size]

/-- NEGATIVE: a cycle through a compound value is rejected. -/
theorem compoundCycle_hasLoop :
    Bindings.hasLoop
      [BindingRel.val "x" (Atom.expr [Atom.sym "f", Atom.var "y"]),
        BindingRel.val "y" (Atom.var "x")] = true := by
  have hclass := Bindings.classValues_eq_lookupVal_toList_of_eqVarsInOrder_nil
    (b := [BindingRel.val "x" (Atom.expr [Atom.sym "f", Atom.var "y"]),
      BindingRel.val "y" (Atom.var "x")]) (by rfl)
  simp (config := { maxSteps := 1000000 }) [Bindings.hasLoop, Bindings.vars,
    Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, hclass, Bindings.lookupVal,
    Bindings.eqRepresentative, Bindings.eqClassOrdered,
    Bindings.eqVarsInOrder, Atom.size, Atom.vars]

end Metta
