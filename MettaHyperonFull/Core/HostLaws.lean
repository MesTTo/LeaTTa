-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.HostLaws
Layer: Core
Purpose: Proof-facing law interfaces for host/native grounded carriers and grounded functions. The
  executable kernel can run concrete builtins directly, but any external host callback used in a
  theorem should provide equality, matching, typing, execution, and display laws through this module
  instead of being treated as an implicit trusted boundary.
Imports: MettaHyperonFull.Core.Grounding, MettaHyperonFull.Core.Matching
Trusted boundary: none. These structures state contracts but introduce no inhabitants or axioms.
Main exports: NativeCarrier, NativeCarrierLaws, GroundingLaws
Open obligations: concrete builtin law instances can be added beside the builtin proofs that need
  them; external callbacks should pass these law records as explicit theorem parameters.
-/
import MettaHyperonFull.Core.Grounding
import MettaHyperonFull.Core.Matching

namespace Metta

/-- A host/native carrier exposed to MeTTa through grounded atoms. The relation fields are part of
    the specification surface: they say what it means for the host equality, matcher, executor, and
    display function to be sound. -/
structure NativeCarrier where
  Carrier : Type
  quote : Carrier -> Ground
  typeOf : Carrier -> Atom
  eqv : Carrier -> Carrier -> Bool
  matchWith : Carrier -> Atom -> List Bindings
  execute : String -> List Atom -> ReduceResult
  display : Carrier -> String
  typeRel : Carrier -> Atom -> Prop
  matchRel : Carrier -> Atom -> Bindings -> Prop
  execRel : String -> List Atom -> ReduceResult -> Prop
  displayRel : Carrier -> String -> Prop

/-- Laws a native carrier must provide before theorem-level code can rely on its host behavior. -/
structure NativeCarrierLaws (N : NativeCarrier) : Prop where
  eq_refl : forall x, N.eqv x x = true
  eq_symm : forall x y, N.eqv x y = true -> N.eqv y x = true
  eq_trans : forall x y z, N.eqv x y = true -> N.eqv y z = true -> N.eqv x z = true
  type_sound : forall x, N.typeRel x (N.typeOf x)
  match_sound : forall x a b, b ∈ N.matchWith x a -> N.matchRel x a b
  execute_sound : forall name args, N.execRel name args (N.execute name args)
  display_sound : forall x, N.displayRel x (N.display x)
  display_eq_of_eq : forall x y, N.eqv x y = true -> N.display x = N.display y

namespace NativeCarrierLaws

theorem typeOf_sound {N : NativeCarrier} (h : NativeCarrierLaws N) (x : N.Carrier) :
    N.typeRel x (N.typeOf x) :=
  h.type_sound x

theorem matchWith_sound {N : NativeCarrier} (h : NativeCarrierLaws N) {x : N.Carrier}
    {a : Atom} {b : Bindings} (hb : b ∈ N.matchWith x a) : N.matchRel x a b :=
  h.match_sound x a b hb

theorem executeSound {N : NativeCarrier} (h : NativeCarrierLaws N) (name : String)
    (args : List Atom) : N.execRel name args (N.execute name args) :=
  h.execute_sound name args

theorem displaySound {N : NativeCarrier} (h : NativeCarrierLaws N) (x : N.Carrier) :
    N.displayRel x (N.display x) :=
  h.display_sound x

end NativeCarrierLaws

/-- Law surface for one concrete grounding entry. It keeps the executable `impl` field separate from
    the proof relation that says which outputs are sound. -/
structure GroundingLaws (g : Grounding) where
  executionRel : List Atom -> ReduceResult -> Prop
  typeSigRel : Atom -> Prop
  execution_sound : forall args, executionRel args (g.impl args)
  typeSig_sound : forall sig, g.typeSig = some sig -> typeSigRel sig

namespace GroundingLaws

theorem impl_sound {g : Grounding} (h : GroundingLaws g) (args : List Atom) :
    h.executionRel args (g.impl args) :=
  h.execution_sound args

theorem typeSig_sound_of_some {g : Grounding} (h : GroundingLaws g) {sig : Atom}
    (hsig : g.typeSig = some sig) : h.typeSigRel sig :=
  h.typeSig_sound sig hsig

end GroundingLaws

end Metta
