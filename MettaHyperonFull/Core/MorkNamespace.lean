-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkNamespace
Layer: Core
Purpose: The query-result variable namespace model used by the MORK bridge. Namespace zero belongs
  to the caller query and preserves caller variables. Data and factor namespaces are stamped with a
  result id so variables from different matches cannot alias.
Imports: MettaHyperonFull.Core.MorkCodec
Trusted boundary: none
Main exports: MorkNamespace.DecodedVar, MorkNamespace.decodeVar
Open obligations: rendering these structured variables back to concrete `VarName` strings with an
  injective printer is a later integration layer.
-/
import MettaHyperonFull.Core.MorkCodec

namespace Metta

namespace MorkNamespace

/-- A decoded query-result variable before it is rendered back to a string variable name. -/
inductive DecodedVar where
  | query : VarName → DecodedVar
  | data : Nat → Nat → Nat → DecodedVar
  deriving Repr, BEq, Inhabited

/-- Decode one variable key from a MORK query result.

Namespace `0` is the caller query namespace and uses the caller's own side table. Other namespaces
carry the query result id, the MORK namespace, and the variable index. -/
def decodeVar (queryVars : List VarName) (resultId ns idx : Nat) : Option DecodedVar :=
  if ns == 0 then
    (MorkCodec.getAt? queryVars idx).map DecodedVar.query
  else
    some (DecodedVar.data resultId ns idx)

end MorkNamespace

end Metta
