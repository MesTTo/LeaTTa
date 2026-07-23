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

/-! ## The conjunctive matcher does not write the world

`matchConj` threads `St` so that stored atoms can be alpha-renamed away from
the query variables, which advances the gensym counter.  It never touches the
world: both of `matchConjAvoiding`'s nested folds rebuild the state with a
counter-only record update.  Stating this here, beside the other world laws,
keeps the fact on the public proof boundary — downstream developments consume
`matchConj_preservesWorld` and never the recursion helper. -/

/-- The recursion helper preserves the world, at every pattern list, state and
solution set. -/
theorem matchConjAvoiding_preservesWorld (atoms : List Atom)
    (patternVars : List VarName) :
    ∀ (patterns : List Atom) (st : St) (sols : List Bindings),
      (matchConjAvoiding atoms patternVars patterns st sols).2.world = st.world := by
  intro patterns
  induction patterns with
  | nil => intro st sols; rfl
  | cons p rest ih =>
      intro st sols
      rw [matchConjAvoiding, ih]
      -- the per-solution fold, and inside it the per-atom fold, are counter-only
      have inner : ∀ (bs : List Bindings) (acc : List Bindings × St),
          (bs.foldl (fun (acc : List Bindings × St) b =>
            let pInst := instantiate b p
            let avoid := b.vars ++ patternVars
            let (ext, st2) := atoms.foldl (fun (a2 : List Bindings × St) atom =>
              let (renamed, nextCounter) := freshenRuleAvoiding a2.2.counter avoid atom atom
              let atom' := renamed.1
              let more := (matchAtoms pInst atom').flatMap fun mb =>
                (Bindings.merge b mb).filter (fun m => !Bindings.hasLoop m)
              (a2.1 ++ more, { a2.2 with counter := nextCounter })) ([], acc.2)
            (acc.1 ++ ext, st2)) acc).2.world = acc.2.world := by
        intro bs
        induction bs with
        | nil => intro acc; rfl
        | cons b rest2 ih2 =>
            intro acc
            simp only [List.foldl_cons]
            rw [ih2]
            have perAtom : ∀ (source : List Atom) (a2 : List Bindings × St),
                (source.foldl (fun (a2 : List Bindings × St) atom =>
                  let (renamed, nextCounter) := freshenRuleAvoiding a2.2.counter
                    (b.vars ++ patternVars) atom atom
                  let atom' := renamed.1
                  let more := (matchAtoms (instantiate b p) atom').flatMap fun mb =>
                    (Bindings.merge b mb).filter (fun m => !Bindings.hasLoop m)
                  (a2.1 ++ more, { a2.2 with counter := nextCounter })) a2).2.world
                  = a2.2.world := by
              intro source
              induction source with
              | nil => intro a2; rfl
              | cons x rest3 ih3 => intro a2; simp only [List.foldl_cons]; rw [ih3]
            exact perAtom atoms _
      exact inner sols ([], st)

/-- **`matchConj` never writes the world.**  The public boundary fact. -/
theorem matchConj_preservesWorld (atoms patterns : List Atom) (st : St)
    (sols : List Bindings) :
    (matchConj atoms patterns st sols).2.world = st.world := by
  rw [matchConj]
  exact matchConjAvoiding_preservesWorld atoms _ patterns st sols

end Metta
