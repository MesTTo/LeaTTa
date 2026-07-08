-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

import MettaHyperonFull.Operational.Trace

namespace Metta

/-- Execution histories are stored as AtomSpace content. -/
def historySpace (tr : Trace) : Space :=
  ⟨tr.states.zipIdx.map (fun (st, i) => Atom.expr [Atom.sym "history", Atom.gnd (Ground.int (Int.ofNat i)), Atom.expr st.output.atoms])⟩

end Metta
