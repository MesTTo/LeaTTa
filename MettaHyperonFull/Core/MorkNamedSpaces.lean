-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.MorkNamedSpaces
Layer: Core
Purpose: Backend-level named spaces for the MORK decoded-observation model. A world maps a space name
  to an encoded space. Adding to one name changes only that name.
Imports: MettaHyperonFull.Core.MorkEncodedSpace
Trusted boundary: none
Main exports: MorkNamedSpaces.NamedSpaces, NamedSpaces.empty, NamedSpaces.selfName,
  NamedSpaces.addAtom, NamedSpaces.query
Open obligations: this is the backend-level visibility model. The minimal interpreter's `World`
  remains the executable runtime model for `&self`, tokens, imports, and state cells.
-/
import MettaHyperonFull.Core.MorkEncodedSpace

namespace Metta

namespace MorkNamedSpaces

/-- A named-space environment as a total map from names to encoded spaces. -/
structure NamedSpaces where
  spaceOf : String → MorkEncodedSpace.EncodedSpace

namespace NamedSpaces

def selfName : String := "&self"

def empty : NamedSpaces :=
  { spaceOf := fun _ => MorkEncodedSpace.EncodedSpace.empty }

/-- Add an atom to exactly one named space. -/
def addAtom (w : NamedSpaces) (name : String) (atom : Atom) : NamedSpaces :=
  { spaceOf := fun queryName =>
      if queryName == name then
        (w.spaceOf queryName).add atom
      else
        w.spaceOf queryName }

def query (w : NamedSpaces) (name : String) (pattern : Atom) : List Bindings :=
  (w.spaceOf name).query pattern

end NamedSpaces

end MorkNamedSpaces

end Metta
