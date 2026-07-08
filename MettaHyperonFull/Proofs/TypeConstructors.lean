-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.TypeConstructors
Layer: Proofs
Purpose: Small laws for the executable type constructors and splitters. `Atom.mkArrow` builds the
  `(-> A1 ... An R)` atom, and `TypeEnv.arrowParts?` recovers its argument types and return type.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none
Main exports: Atom.isArrow_mkArrow, TypeEnv.arrowParts?_mkArrow, TypeEnv.arrowParts?_sym,
  TypeEnv.arrowParts?_var, TypeEnv.arrowParts?_gnd, TypeEnv.arrowParts?_empty_expr,
  TypeEnv.arrowParts?_arrow_no_return
Open obligations: none
-/
import MettaHyperonFull.Proofs.Basic

namespace Metta

namespace Atom

/-- Arrow atoms built by `Atom.mkArrow` are recognized by the executable arrow predicate. -/
theorem isArrow_mkArrow (args : List Atom) (ret : Atom) :
    isArrow (mkArrow args ret) = true := rfl

end Atom

namespace TypeEnv

/-- Splitting an arrow built by `Atom.mkArrow` recovers the original arguments and return type. -/
theorem arrowParts?_mkArrow (args : List Atom) (ret : Atom) :
    arrowParts? (Atom.mkArrow args ret) = some (args, ret) := by
  simp [Atom.mkArrow, arrowParts?, List.reverse_append]

theorem arrowParts?_sym (s : String) : arrowParts? (Atom.sym s) = none := rfl

theorem arrowParts?_var (v : VarName) : arrowParts? (Atom.var v) = none := rfl

theorem arrowParts?_gnd (g : Ground) : arrowParts? (Atom.gnd g) = none := rfl

theorem arrowParts?_empty_expr : arrowParts? (Atom.expr []) = none := rfl

/-- `(->)` with no return type is not a valid arrow type. -/
theorem arrowParts?_arrow_no_return : arrowParts? (Atom.expr [Atom.sym "->"]) = none := rfl

end TypeEnv

end Metta
