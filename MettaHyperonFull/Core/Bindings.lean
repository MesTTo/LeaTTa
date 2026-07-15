-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.Bindings
Layer: Core
Purpose: The binding sets that matching and unification produce. A binding set is a conjunction of
  variable-binding relations, comprising value bindings and variable aliases (Hyperon's `Bindings`).
  Provides lookup, alias classes, removal, loop detection, and the raw insertion primitives. The
  consistency-checking merge lives in Matching.lean.
Imports: MettaHyperonFull.Core.Atom, MettaHyperonFull.Core.Pretty
Trusted boundary: none
Main exports: BindingRel, Bindings, Bindings.empty, Bindings.lookupVal, Bindings.eqClassOrdered,
  Bindings.classValues, Bindings.resolve, Bindings.resolveAtom, Bindings.removeVal,
  Bindings.hasLoop, Bindings.addValRaw, Bindings.addEqRaw
Open obligations: none
-/
import MettaHyperonFull.Core.Atom
import MettaHyperonFull.Core.Pretty

namespace Metta

/-- A variable-binding relation. `val x a` is `$x ← a`; `eq x y` is `$x = $y`. -/
inductive BindingRel where
  | val : VarName → Atom → BindingRel
  | eq : VarName → VarName → BindingRel
  deriving Repr, BEq, Inhabited

/-- A binding set: a conjunction of variable-binding relations, comprising value bindings `$x ← a` and
    `$x = $y` aliases (Hyperon's `Bindings`, the output of matching/unification). -/
abbrev Bindings := List BindingRel

namespace Bindings

def empty : Bindings := []

/-- The atom bound to `$x` by a direct `val` relation, if any (`eq` aliases are not followed). -/
def lookupVal (b : Bindings) (x : VarName) : Option Atom :=
  match b with
  | [] => none
  | BindingRel.val y a :: rest => if x == y then some a else lookupVal rest x
  | _ :: rest => lookupVal rest x

/-- One saturation pass for the symmetric equality closure. -/
def eqStep (b : Bindings) (acc : List VarName) : List VarName :=
  b.foldl (fun acc r => match r with
    | BindingRel.eq x y =>
        let acc := if acc.contains x && !acc.contains y then acc ++ [y] else acc
        if acc.contains y && !acc.contains x then acc ++ [x] else acc
    | _ => acc) acc

/-- Fuelled saturation of the symmetric-transitive equality closure. -/
def eqClassAux (b : Bindings) : Nat → List VarName → List VarName
  | 0, acc => acc
  | fuel + 1, acc => eqClassAux b fuel (eqStep b acc)

/-- All variables explicitly equality-connected to `x`, including `x`. -/
def eqClass (b : Bindings) (x : VarName) : List VarName :=
  eqClassAux b (2 * b.length + 1) [x]

/-- Variables mentioned by equality relations, in representative order. Raw
    relations are newest-first, while matcher equalities store the rule endpoint
    before the query endpoint, so oldest edges and their query endpoints come first. -/
def eqVarsInOrder (b : Bindings) : List VarName :=
  b.reverse.foldl (fun acc r => match r with
    | BindingRel.eq x y =>
        let acc := if acc.contains y then acc else acc ++ [y]
        if acc.contains x then acc else acc ++ [x]
    | _ => acc) []

/-- The equality class of `x` in stable relation order. -/
def eqClassOrdered (b : Bindings) (x : VarName) : List VarName :=
  match (eqVarsInOrder b).filter (fun y => (eqClass b x).contains y) with
  | [] => [x]
  | cls => cls

/-- Stable representative of `x`'s explicit equality class. -/
def eqRepresentative (b : Bindings) (x : VarName) : VarName :=
  (eqClassOrdered b x).headD x

/-- Every direct value carried by a member of `x`'s equality class, in stable
    class-member order. Direct lookup selects the unique normalized value for
    each member, so raw relation-list permutations do not steer reconciliation. -/
def classValues (b : Bindings) (x : VarName) : List Atom :=
  (eqClassOrdered b x).filterMap (lookupVal b)

@[simp] theorem classValues_empty (x : VarName) :
    classValues [] x = [] := by
  simp [classValues, eqClassOrdered, eqVarsInOrder, lookupVal]

@[simp] theorem classValues_singleton_val_self
    (x : VarName) (value : Atom) :
    classValues [BindingRel.val x value] x = [value] := by
  simp [classValues, eqClassOrdered, eqVarsInOrder, lookupVal]

@[simp] theorem classValues_singleton_val_ne
    {key x : VarName} (value : Atom) (h : x ≠ key) :
    classValues [BindingRel.val key value] x = [] := by
  simp [classValues, eqClassOrdered, eqVarsInOrder, lookupVal, h]

theorem classValues_eq_lookupVal_toList_of_eqVarsInOrder_nil
    {b : Bindings} (horder : eqVarsInOrder b = []) (x : VarName) :
    classValues b x = (lookupVal b x).toList := by
  unfold classValues
  rw [show eqClassOrdered b x = [x] by
    simp [eqClassOrdered, horder]]
  cases hlookup : lookupVal b x <;> simp [hlookup]

/-- Variables participating in a binding relation, including variables nested in values. -/
def vars (b : Bindings) : List VarName :=
  (b.flatMap fun r => match r with
    | BindingRel.val x a => x :: a.vars
    | BindingRel.eq x y => [x, y]).eraseDups

/-- The contribution of one stored relation to recursive resolution fuel. -/
def relationResolutionFuel : BindingRel → Nat
  | BindingRel.val _ value => value.size + 1
  | BindingRel.eq _ _ => 1

/-- Structural fuel sufficient for traversing every stored value and relation. -/
def resolutionFuel (b : Bindings) (a : Atom) : Nat :=
  a.size + (b.map relationResolutionFuel).sum + 1

/-- Resolve every variable in an atom through equality classes and class values.
    `none` means a cyclic class/value dependency was encountered. Unknown variables
    remain variables, matching Hyperon's recursive resolution behavior. -/
def resolveAtomAux (b : Bindings) : Nat → List VarName → Atom → Option Atom
  | 0, _, _ => none
  | fuel + 1, visited, atom =>
      match atom with
      | Atom.var x =>
          let cls := eqClassOrdered b x
          if cls.any visited.contains then none
          else
            match classValues b x with
            | [] => some (Atom.var (eqRepresentative b x))
            | value :: _ =>
                match value with
                | Atom.var y =>
                    if cls.contains y then
                      if cls.length == 1 then none
                      else some (Atom.var (eqRepresentative b x))
                    else resolveAtomAux b fuel (cls ++ visited) value
                | _ => resolveAtomAux b fuel (cls ++ visited) value
      | Atom.expr xs =>
          match xs.mapM (resolveAtomAux b fuel visited) with
          | some ys => some (Atom.expr ys)
          | none => none
      | other => some other

/-- Resolve a bound variable through its full equality class and recursively through
    compound values. Returns `none` for an unbound variable or a dependency loop. -/
def resolve (b : Bindings) (x : VarName) : Option Atom :=
  let cls := eqClassOrdered b x
  if cls == [x] && (classValues b x).isEmpty then none
  else resolveAtomAux b (resolutionFuel b (Atom.var x)) [] (Atom.var x)

/-- Resolve every variable occurrence in `a` through its full equality class.
    A cyclic variable occurrence remains unchanged; runtime paths reject the
    containing binding set with `hasLoop` before instantiation. -/
def resolveAtom (b : Bindings) : Atom → Atom
  | Atom.var x => (resolve b x).getD (Atom.var x)
  | Atom.expr xs => Atom.expr (xs.map (resolveAtom b))
  | other => other

/-- The variables directly equated with `$x` by `eq` relations (one hop, both orientations). -/
def eqClasses (b : Bindings) (x : VarName) : List VarName :=
  b.foldl (fun acc r => match r with
    | BindingRel.eq a c => if a == x then c :: acc else if c == x then a :: acc else acc
    | _ => acc) []

/-- Remove direct value bindings for variable `x`; equality relations remain. -/
def removeVal (b : Bindings) (x : VarName) : Bindings :=
  b.filter (fun r => match r with | BindingRel.val y _ => y != x | _ => true)

/-- True when any variable participates in a direct self-loop or a longer cyclic
    dependency through equality classes, variable chains, or compound values. -/
def hasLoop (b : Bindings) : Bool :=
  b.any (fun r => match r with
    | BindingRel.val x (Atom.var y) => x == y
    | BindingRel.eq x y => x == y
    | _ => false) ||
  (vars b).any (fun x =>
    (resolveAtomAux b (resolutionFuel b (Atom.var x)) [] (Atom.var x)).isNone)

/-- Bind `$x ← a`, dropping any previous value binding for `$x`. Raw: no occurs/consistency check
    (that is `addVarBinding`'s job). -/
def addValRaw (b : Bindings) (x : VarName) (a : Atom) : Bindings := BindingRel.val x a :: removeVal b x

/-- Add the alias `$x = $y` (a no-op when `x = y`). Raw: no consistency check. -/
def addEqRaw (b : Bindings) (x y : VarName) : Bindings := if x == y then b else BindingRel.eq x y :: b

end Bindings

end Metta
