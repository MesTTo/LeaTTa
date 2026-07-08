-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.WorldLaws
Layer: Proofs
Purpose: Visibility laws for the mutable world threaded by the minimal interpreter: named-space
  creation and append, state-cell updates, token binding, and self-space append/remove.
Imports: MettaHyperonFull.Proofs.SpaceLaws
Trusted boundary: none
Main exports: World.setStore_visible, World.newSpace_visible, World.appendSpace_visible,
  World.bindTok_visible, World.appendSelf_visible, World.eraseSelf_after_append_single
Open obligations: instruction-level add-atom/change-state visibility can cite these world laws and
  the corresponding `interpretStack1` cases.
-/
import MettaHyperonFull.Proofs.SpaceLaws

namespace Metta
open Metta.Minimal

namespace World

open Std

theorem setStore_visible (w : World) (id : Nat) (v : Atom) :
    (w.setStore id v).store[id]? = some v := by
  simp [World.setStore]

theorem newSpace_visible (w : World) (name : String) :
    (w.newSpace name).spaces.getD name [] = [] := by
  simp [World.newSpace, Std.HashMap.getD_eq_getD_getElem?]

theorem appendSpace_visible (w : World) (name : String) (atoms : List Atom) :
    (w.appendSpace name atoms).spaces.getD name [] = w.spaces.getD name [] ++ atoms := by
  simp [World.appendSpace, Std.HashMap.getD_eq_getD_getElem?]

theorem bindTok_visible (w : World) (name : String) (value : Atom) :
    (w.bindTok name value).tokens[name]? = some value := by
  simp [World.bindTok]

theorem appendSelf_visible (w : World) (atoms : List Atom) :
    (w.appendSelf atoms).selfExtra = w.selfExtra ++ atoms := by
  rfl

theorem appendSelfImport_visible (w : World) (atoms : List Atom) :
    (w.appendSelfImport atoms).selfImports = w.selfImports ++ atoms := by
  rfl

theorem markImport_visible (w : World) (target moduleName : String) :
    (w.markImport target moduleName).imported =
      World.importKey target moduleName :: w.imported := by
  rfl

theorem eraseSelf_visible (w : World) (a : Atom) :
    (w.eraseSelf a).selfExtra = w.selfExtra.erase a := by
  rfl

end World

end Metta
