-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational.MinimalCoverage
Layer: Operational
Purpose: Checked examples for the minimal-instruction dispatcher. Each `MinimalInstr` name is parsed,
  each implemented `evalMinimal` form has an exact executable result, and the intentional passthrough
  forms are recorded as such. The examples are small on purpose: they make fallthrough bugs visible
  without turning the operational spec into a test framework.
Imports: MettaHyperonFull.Operational.Minimal
Trusted boundary: none
Main exports: (examples only)
Open obligations: none

Source notes:
- Meredith, Goertzel, Warrell, and Vandervorst, "Meta-MeTTa: an operational semantics for MeTTa",
  arXiv:2305.17218, for the small-step operational model and instruction vocabulary.
- The Hyperon and MeTTa documentation, for surface names such as `chain`, `collapse-bind`, `superpose`,
  and context-space.
- The executable kernel in `MettaHyperonFull.Minimal.Interpreter`, for the fuller `metta` family that
  is deliberately outside this small operational dispatcher.
-/
import MettaHyperonFull.Operational.Minimal

namespace Metta

private abbrev cfg : RuntimeConfig := default
private abbrev emptyCtx : Space := Space.empty

/-! ### Name coverage -/

example : minimalInstrOf? (Atom.sym "eval") = some MinimalInstr.eval := rfl
example : minimalInstrOf? (Atom.sym "evalc") = some MinimalInstr.evalc := rfl
example : minimalInstrOf? (Atom.sym "chain") = some MinimalInstr.chain := rfl
example : minimalInstrOf? (Atom.sym "unify") = some MinimalInstr.unify := rfl
example : minimalInstrOf? (Atom.sym "decons-atom") = some MinimalInstr.deconsAtom := rfl
example : minimalInstrOf? (Atom.sym "cons-atom") = some MinimalInstr.consAtom := rfl
example : minimalInstrOf? (Atom.sym "function") = some MinimalInstr.function := rfl
example : minimalInstrOf? (Atom.sym "return") = some MinimalInstr.ret := rfl
example : minimalInstrOf? (Atom.sym "collapse-bind") = some MinimalInstr.collapseBind := rfl
example : minimalInstrOf? (Atom.sym "superpose-bind") = some MinimalInstr.superposeBind := rfl
example : minimalInstrOf? (Atom.sym "metta") = some MinimalInstr.metta := rfl
example : minimalInstrOf? (Atom.sym "context-space") = some MinimalInstr.contextSpace := rfl
example : minimalInstrOf? (Atom.sym "call-native") = some MinimalInstr.callNative := rfl
example : minimalInstrOf? (Atom.sym "unknown") = none := rfl

/-! ### Implemented dispatcher forms -/

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "unify", Atom.sym "a", Atom.var "x", Atom.var "x", Atom.sym "bad"])
      = [Atom.sym "a"] := by
  simp [cfg, emptyCtx, evalMinimal, evalUnifyInstr, matchAtoms, matchAtomsWith, instantiate,
    Bindings.resolveAtom, Bindings.resolve, Bindings.resolveAtomAux, Bindings.resolutionFuel,
    Bindings.relationResolutionFuel, Bindings.classValues, Bindings.eqClassOrdered,
    Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep, Bindings.eqVarsInOrder,
    Bindings.lookupVal, Bindings.eqRepresentative, List.filterMap,
    Subst.occurs, Atom.size]

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "unify", Atom.sym "a", Atom.sym "b", Atom.sym "ok", Atom.sym "bad"])
      = [Atom.sym "bad"] := rfl

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "chain",
        Atom.expr [Atom.sym "superpose-bind", Atom.expr [Atom.sym "a", Atom.sym "b"]],
        Atom.var "x",
        Atom.expr [Atom.sym "pair", Atom.var "x"]])
      = [Atom.expr [Atom.sym "pair", Atom.sym "a"], Atom.expr [Atom.sym "pair", Atom.sym "b"]] := by
  simp [cfg, emptyCtx, evalMinimal, chainResults, Subst.apply, Subst.lookup]

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "cons-atom", Atom.sym "h", Atom.expr [Atom.sym "t"]])
      = [Atom.expr [Atom.sym "h", Atom.sym "t"]] := rfl

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "decons-atom", Atom.expr [Atom.sym "h", Atom.sym "t"]])
      = [Atom.expr [Atom.sym "h", Atom.expr [Atom.sym "t"]]] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "collapse-bind", Atom.sym "x"])
      = [Atom.expr [Atom.sym "x"]] := rfl

example :
    evalMinimal cfg emptyCtx
      (Atom.expr [Atom.sym "superpose-bind", Atom.expr [Atom.sym "a", Atom.sym "b"]])
      = [Atom.sym "a", Atom.sym "b"] := rfl

example : evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "eval", Atom.sym "x"]) = [Atom.sym "x"] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "evalc", Atom.sym "x", Atom.sym "T"])
      = [Atom.sym "x"] := rfl

example : evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "return", Atom.sym "x"]) = [Atom.sym "x"] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "function", Atom.expr [Atom.sym "return", Atom.sym "x"]])
      = [Atom.sym "x"] := rfl

example :
    evalMinimal cfg ⟨[Atom.sym "k"]⟩ (Atom.expr [Atom.sym "context-space"])
      = [Atom.expr [Atom.sym "k"]] := rfl

/-! ### Intentional passthrough and malformed forms -/

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "metta", Atom.sym "x", Atom.sym "T", Atom.sym "S"])
      = [Atom.expr [Atom.sym "metta", Atom.sym "x", Atom.sym "T", Atom.sym "S"]] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "call-native", Atom.sym "host", Atom.sym "x"])
      = [Atom.expr [Atom.sym "call-native", Atom.sym "host", Atom.sym "x"]] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "cons-atom", Atom.sym "h", Atom.sym "not-list"])
      = [Atom.expr [Atom.sym "cons-atom", Atom.sym "h", Atom.sym "not-list"]] := rfl

example :
    evalMinimal cfg emptyCtx (Atom.expr [Atom.sym "decons-atom", Atom.expr []])
      = [Atom.expr [Atom.sym "decons-atom", Atom.expr []]] := rfl

end Metta
