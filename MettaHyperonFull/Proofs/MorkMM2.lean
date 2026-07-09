-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.MorkMM2
Layer: Proofs
Purpose: First semantic readback laws for MORK MM2 exec. A selected exec rule is consumed even when
  it produces no rows.
Imports: MettaHyperonFull.Proofs.QueryBackend, MettaHyperonFull.Core.MorkMM2
Trusted boundary: none
Main exports: MorkMM2.step_consumes_first_exec, MorkMM2.step_no_exec,
  MorkMM2.step_no_match_space
Open obligations: concrete encoded priority order, add/remove effects, and fixpoint scheduling remain
  above this semantic readback.
-/
import MettaHyperonFull.Proofs.QueryBackend
import MettaHyperonFull.Core.MorkMM2

namespace Metta

namespace MorkMM2

/-- With no exec rules, one step is the identity. -/
theorem step_no_exec (space : Space) :
    step ⟨space, []⟩ = ⟨space, []⟩ := rfl

/-- A selected exec rule is consumed after one step. -/
theorem step_consumes_first_exec (space : Space) (rule : ExecRule) (rest : List ExecRule) :
    (step ⟨space, rule :: rest⟩).execs = rest := rfl

/-- If the selected rule has no rows, it is still consumed and the fact space is unchanged. -/
theorem step_no_match_space {space : Space} {rule : ExecRule} {rest : List ExecRule}
    (h : rows space rule = []) :
    (step ⟨space, rule :: rest⟩).space = space := by
  simp [step, producedAtoms, insertProduced, h]

end MorkMM2

end Metta
