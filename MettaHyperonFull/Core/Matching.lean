-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.Matching
Layer: Core
Purpose: Nondeterministic pattern matching for MeTTa atoms and the consistency-checking merge of
  binding sets. Matching follows the official left/right style: variables on either side produce
  bindings, expressions match pointwise, and a runtime-supplied custom matcher handles grounded atoms.
  Merge combines two binding sets into all their consistent unions (Hyperon's `Bindings::merge`), using
  unification to reconcile conflicting values.
Imports: MettaHyperonFull.Core.Unification, MettaHyperonFull.Core.Bindings
Trusted boundary: none
Main exports: GroundMatcher, Bindings.addVarBinding, Bindings.addVarEquality, Bindings.mergeOne,
  Bindings.merge, Bindings.ofSubst, Bindings.reconcileAll, Bindings.rebuildFromSubst,
  Bindings.reconciliationAliases, Bindings.rebuildFromReconciliation,
  matchAtomsWith, matchAll, matchAtoms, bindingsToSubst, instantiate
Open obligations: none
-/
import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.Bindings

namespace Metta

/-- A custom matcher for grounded atoms. It may be nondeterministic. -/
abbrev GroundMatcher := Atom → Atom → List Bindings

/- Binding-set merge based on the algorithm in the Hyperon specification. -/
namespace Bindings

/-- View a unifier as binding relations, preserving variable/variable constraints
    as explicit equality rather than an oriented value assignment. -/
def ofSubst (s : Subst) : Bindings :=
  s.map (fun p => match p.2 with
    | Atom.var y => BindingRel.eq p.1 y
    | value => BindingRel.val p.1 value)

/-- Add every relation from a unifier to a binding set without discarding its
    reconciliation constraints. -/
def addSubstRaw (b : Bindings) (s : Subst) : Bindings :=
  (ofSubst s).foldl (fun b r => match r with
    | BindingRel.val x value => addValRaw b x value
    | BindingRel.eq x y => addEqRaw b x y) b

/-- Unify all values carried by one equality class. -/
def unifyValues : List Atom → Option Subst
  | [] => some []
  | [_] => some []
  | first :: rest =>
      let equations := rest.map (fun value => (first, value))
      let fuel := first.size + (rest.map Atom.size).sum
      Unify.unifyRounds fuel equations []

/-- Present one binding relation as a first-order atom equation. -/
def relationEquation : BindingRel → Atom × Atom
  | BindingRel.val x value => (Atom.var x, value)
  | BindingRel.eq x y => (Atom.var x, Atom.var y)

/-- The complete first-order equation presentation of a binding set. -/
def equations (b : Bindings) : List (Atom × Atom) :=
  b.map relationEquation

/-- Structural fuel covering every atom in an equation worklist. -/
def equationFuel (work : List (Atom × Atom)) : Nat :=
  (work.map fun equation => equation.1.size + equation.2.size).sum

/-- Reconcile every existing binding relation together with new constraints.
    This prevents a class-local unifier from overwriting an unrelated seeded
    value that shares one of its internal variables. -/
def reconcileAll (b : Bindings) (extra : List (Atom × Atom)) : Option Subst :=
  let work := equations b ++ extra
  Unify.unifyRounds (equationFuel work) work []

/-- Retain the explicit equality graph while a whole-system unifier normalizes
    every direct value relation. -/
def equalitySkeleton : Bindings → Bindings
  | [] => []
  | BindingRel.val _ _ :: rest => equalitySkeleton rest
  | BindingRel.eq x y :: rest => BindingRel.eq x y :: equalitySkeleton rest

/-- Rebuild a normalized binding set without discarding explicit class edges. -/
def rebuildFromSubst (b : Bindings) (sigma : Subst) : Bindings :=
  equalitySkeleton b ++ ofSubst sigma

/-- Every explicit variable alias encountered by whole-system reconciliation.
The primary trace preserves the successful run's elimination order.  The
collision-first trace exposes aliases inside newly joined compound values
before seeded ground equations can normalize them away. -/
def reconciliationAliases
    (b : Bindings) (extra : List (Atom × Atom)) (_sigma : Subst) :
    List (VarName × VarName) :=
  let primary := equations b ++ extra
  let collisionFirst := extra ++ equations b
  Unify.aliasTrace (equationFuel primary) primary ++
    Unify.aliasTrace (equationFuel collisionFirst) collisionFirst

/-- Insert one alias only when its equality class is not already represented.
This makes alias restoration conservative on existing normalized outputs. -/
def restoreAlias (b : Bindings) (edge : VarName × VarName) : Bindings :=
  if (eqClass b edge.1).contains edge.2 then b
  else addEqRaw b edge.1 edge.2

/-- Rebuild normalized values while retaining every alias discovered by a
successful whole-system reconciliation.  Existing output is left
unchanged whenever its equality closure already carries the alias. -/
def rebuildFromReconciliation
    (candidate source : Bindings) (extra : List (Atom × Atom))
    (sigma : Subst) : Bindings :=
  (reconciliationAliases source extra sigma).foldl restoreAlias
    (rebuildFromSubst candidate sigma)

/-- Add the alias `$x = $y` while reconciling every value already carried by
    either equality class. Successful unifiers are retained as relations. -/
def addVarEquality (b : Bindings) (x y : VarName) : List Bindings :=
  let candidate := addEqRaw b x y
  match unifyValues (classValues candidate x) with
  | none => []
  | some [] => [candidate]
  | some (_ :: _) =>
      match reconcileAll b [(Atom.var x, Atom.var y)] with
      | none => []
      | some sigma =>
          [rebuildFromReconciliation candidate b
            [(Atom.var x, Atom.var y)] sigma]

/-- Add `$x ← v` consistently across `$x`'s whole equality class. Variable
    values are aliases, and successful reconciliation constraints are retained
    instead of replacing one direct value and discarding the unifier. -/
def addVarBinding (b : Bindings) (x : VarName) (v : Atom) : List Bindings :=
  match v with
  | Atom.var y => addVarEquality b x y
  | _ =>
      match classValues b x with
      | [] => [addValRaw b x v]
      | values =>
          match unifyValues (values ++ [v]) with
          | none => []
          | some [] => [b]
          | some (_ :: _) =>
              match reconcileAll b [(Atom.var x, v)] with
              | none => []
              | some sigma =>
                  [rebuildFromReconciliation b b [(Atom.var x, v)] sigma]

/-- Fold one binding relation `r` into every candidate set in `bs`, keeping only consistent
    extensions; it is nondeterministic, so a relation may yield zero, one, or several results. -/
def mergeOne (bs : List Bindings) (r : BindingRel) : List Bindings :=
  bs.flatMap (fun b => match r with
    | BindingRel.val x v => addVarBinding b x v
    | BindingRel.eq x y => addVarEquality b x y)

/-- Combine two binding sets into all their consistent unions (Hyperon's `Bindings::merge`); the
    result is empty exactly when they conflict. -/
def merge (a b : Bindings) : List Bindings := b.foldl mergeOne [a]

end Bindings

mutual

/-- Match atoms in the official left/right style. Variables on either side produce bindings;
    expression matching is pointwise; grounded custom matching can be supplied by the runtime. When
    only the right-hand atom is grounded, the custom matcher is called as `f r l`, arguments swapped. -/
def matchAtomsWith (custom : Option GroundMatcher) : Atom → Atom → List Bindings
  | Atom.sym a, Atom.sym b => if a == b then [[]] else []
  | Atom.var x, Atom.var y => if x == y then [[]] else [[BindingRel.eq x y]]
  | Atom.var x, r => if Subst.occurs x r then [] else [[BindingRel.val x r]]
  | l, Atom.var y => if Subst.occurs y l then [] else [[BindingRel.val y l]]
  | Atom.expr xs, Atom.expr ys => matchAll custom [[]] xs ys
  | l@(Atom.gnd _), r => match custom with | some f => f l r | none => if Atom.equiv l r then [[]] else []
  | l, r@(Atom.gnd _) => match custom with | some f => f r l | none => if Atom.equiv l r then [[]] else []
  | l, r => if Atom.equiv l r then [[]] else []

/-- Pointwise-match two atom lists, threading the consistent binding sets accumulated so far
    (`acc`). Each completed child match is pruned before merge-back, while the public `matchAtoms`
    boundary below performs the same check on the completed whole result. Lists of different
    lengths do not match. -/
def matchAll (custom : Option GroundMatcher) (acc : List Bindings) : List Atom → List Atom → List Bindings
  | [], [] => acc
  | x :: xs, y :: ys =>
      let subs := (matchAtomsWith custom x y).filter (fun bindings => !bindings.hasLoop)
      matchAll custom (acc.flatMap (fun a => subs.flatMap (fun b => Bindings.merge a b))) xs ys
  | _, _ => []

end

/-- Match pattern `l` against `r` with the default matcher (no custom grounded
    matching), returning every acyclic binding set under which they unify.

    The recursive matcher deliberately builds candidates before the complete
    dependency graph is known.  The published `match_atoms` contract and
    Hyperon's public matcher both reject whole-result variable loops here. -/
def matchAtoms (l r : Atom) : List Bindings :=
  (matchAtomsWith none l r).filter (fun bindings => !bindings.hasLoop)

/-- Apply a binding set as a substitution. Equality-only relations do not choose an orientation;
    value bindings do. -/
def bindingsToSubst (b : Bindings) : Subst :=
  b.foldr (fun r s => match r with | BindingRel.val x v => (x,v)::s | _ => s) []

/-- Resolve a binding set throughout an atom, including equality classes,
    variable chains, and variables nested in compound values. -/
def instantiate (b : Bindings) (a : Atom) : Atom := Bindings.resolveAtom b a

end Metta
