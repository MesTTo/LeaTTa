-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkMM2
Layer: Core
Purpose: A small semantic readback model for MORK MM2 `exec` rules. The first exec rule is consumed,
  its pattern list is matched by serial conjunctive query, and its templates are instantiated into the
  space.
Imports: MettaHyperonFull.Core.QueryBackend
Trusted boundary: none
Main exports: MorkMM2.ExecRule, MorkMM2.ExecState, MorkMM2.producedAtoms, MorkMM2.step, MorkMM2.run
Open obligations: concrete encoded priority order, `I`/`,` and `O`/`,` parsing, and add/remove
  template effects are implementation layers above this semantic model.
-/
import MettaHyperonFull.Core.QueryBackend

namespace Metta

namespace MorkMM2

/-- A semantic MM2 exec rule: match all patterns, then instantiate all templates. -/
structure ExecRule where
  loc : Nat
  patterns : List Atom
  templates : List Atom
  deriving Repr, BEq, Inhabited

/-- MM2 state split into ordinary facts and pending exec rules. -/
structure ExecState where
  space : Space
  execs : List ExecRule
  deriving Repr, BEq, Inhabited

/-- Rows produced by the serial conjunctive query for a rule. -/
def rows (space : Space) (rule : ExecRule) : List Bindings :=
  QueryBackend.serialQueryMultiRows (fun pattern => space.query pattern) rule.patterns

/-- Atoms produced by instantiating every template under every row. -/
def producedAtoms (space : Space) (rule : ExecRule) : List Atom :=
  (rows space rule).flatMap (fun row => rule.templates.map (fun template => instantiate row template))

/-- Insert a list of produced atoms into a space. -/
def insertProduced (space : Space) (atoms : List Atom) : Space :=
  atoms.foldl Space.insert space

/-- Consume and fire the first exec rule, if any. -/
def step : ExecState → ExecState
  | ⟨space, []⟩ => ⟨space, []⟩
  | ⟨space, rule :: rest⟩ => ⟨insertProduced space (producedAtoms space rule), rest⟩

/-- Run at most `fuel` MM2 exec steps. -/
def run : Nat → ExecState → ExecState
  | 0, state => state
  | n + 1, state => run n (step state)

end MorkMM2

end Metta
