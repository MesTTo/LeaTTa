-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Minimal.CaptureAvoidingFreshening
Layer: Minimal
Purpose: Capture-avoiding alpha-renaming for the string-named variables used by the minimal
  interpreter. The legacy counter suffix remains available for compatibility and is used whenever
  it is already disjoint from the caller's live names. A finite, injective fallback is used exactly
  when a visible spelling would collide.
Imports: MettaHyperonFull.Core.Matching
Trusted boundary: none
Main exports: freshenRule, freshenAtom, renameAllVars, captureAvoidingName, freshenRuleAvoiding
Open obligations: none

Reference note: upstream Hyperon attaches a process-global numeric identity to `VariableAtom` and
`make_variables_unique` refreshes that hidden identity. This model represents identity solely by a
string, so alpha-renaming must explicitly avoid every live spelling to implement the same
capture-avoiding intent.
-/
import MettaHyperonFull.Core.Matching

namespace Metta.Minimal
open Metta

/-- The original counter-suffix freshening. It remains public both as a compatibility operation and
as the executable witness used by regression tests for the formerly capture-prone behavior. -/
def freshenRule (counter : Nat) (lhs rhs : Atom) : Atom × Atom :=
  match Atom.vars lhs ++ Atom.vars rhs with
  | [] => (lhs, rhs)
  | vs =>
      let sub : Subst := vs.map fun v => (v, Atom.var (v ++ "#" ++ toString counter))
      (Subst.apply sub lhs, Subst.apply sub rhs)

/-- The original single-atom counter-suffix freshening. -/
def freshenAtom (counter : Nat) (a : Atom) : Atom :=
  match Atom.vars a with
  | [] => a
  | vs =>
      let sub : Subst := vs.map fun v => (v, Atom.var (v ++ "#" ++ toString counter))
      Subst.apply sub a

/-- Rename every variable leaf by a total name function. -/
def renameAllVars (f : VarName → VarName) : Atom → Atom
  | Atom.sym s => Atom.sym s
  | Atom.var v => Atom.var (f v)
  | Atom.gnd g => Atom.gnd g
  | Atom.expr xs => Atom.expr (xs.map (renameAllVars f))

/-- A prefix longer than every name in a finite avoid set. -/
def avoidancePrefix (avoid : List VarName) : String :=
  String.ofList (List.replicate ((avoid.map String.length).sum + 1) '#')

/-- The injective fallback spelling used when the legacy suffix would capture a live name. -/
def captureAvoidingName (avoid : List VarName) (counter : Nat) (v : VarName) : VarName :=
  avoidancePrefix avoid ++ v ++ "#" ++ toString counter

/-- Capture-avoiding rule freshening. The avoid set is finite and supplied by the evaluator from
the live binding keys and values, query atoms, and continuation stack. The next counter is always
`counter + 1`, preserving the evaluator's existing candidate-count arithmetic. When the legacy
counter suffix is already fresh, its exact output is retained; otherwise an injective long-prefix
renaming is used. -/
def freshenRuleAvoiding
    (counter : Nat) (avoid : List VarName) (lhs rhs : Atom) : (Atom × Atom) × Nat :=
  let legacy := freshenRule counter lhs rhs
  if ∃ v ∈ legacy.1.vars ++ legacy.2.vars, v ∈ avoid then
    let f := captureAvoidingName avoid counter
    ((renameAllVars f lhs, renameAllVars f rhs), counter + 1)
  else
    (legacy, counter + 1)

end Metta.Minimal
