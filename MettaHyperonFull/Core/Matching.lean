import MettaHyperonFull.Core.Unification
import MettaHyperonFull.Core.Bindings

namespace Metta

/-- A custom matcher for grounded atoms. It may be nondeterministic. -/
abbrev GroundMatcher := Atom → Atom → List Bindings

/- Binding-set merge based on the algorithm in the Hyperon specification. -/
namespace Bindings

/-- Add `$x ← v` to `b` consistently: if `$x` is unbound, insert it; if already bound to `v`, keep
    `b`; otherwise the old and new values must unify (else no result). The consistency-checking core
    of `merge`. -/
def addVarBinding (b : Bindings) (x : VarName) (v : Atom) : List Bindings :=
  match lookupVal b x with
  | none => [addValRaw b x v]
  | some prev =>
      if prev == v then [b]
      else match Unify.unifyTop prev v with
        | none => []
        | some _ => [addValRaw b x v]

/-- Add the alias `$x = $y` to `b` consistently: if both are already value-bound, those values must
    be equal (else no result). -/
def addVarEquality (b : Bindings) (x y : VarName) : List Bindings :=
  match lookupVal b x, lookupVal b y with
  | some vx, some vy => if vx == vy then [addEqRaw b x y] else []
  | _, _ => [addEqRaw b x y]

/-- Fold one binding relation `r` into every candidate set in `bs`, keeping only consistent
    extensions; it is nondeterministic, so a relation may yield zero, one, or several results. -/
def mergeOne (bs : List Bindings) (r : BindingRel) : List Bindings :=
  bs.flatMap (fun b => match r with
    | BindingRel.val x v => addVarBinding b x v
    | BindingRel.eq x y => addVarEquality b x y)

/-- Combine two binding sets into all their consistent unions (Hyperon's `Bindings::merge`); the
    result is empty exactly when they conflict. -/
def merge (a b : Bindings) : List Bindings := b.foldl mergeOne [a]

/-- View a substitution as a binding set: each `x ↦ v` becomes a `val` relation. -/
def ofSubst (s : Subst) : Bindings := s.map (fun p => BindingRel.val p.fst p.snd)

end Bindings

mutual

/-- Match atoms in the official left/right style. Variables on either side produce bindings;
    expression matching is pointwise; grounded custom matching can be supplied by the runtime. -/
def matchAtomsWith (custom : Option GroundMatcher) : Atom → Atom → List Bindings
  | Atom.sym a, Atom.sym b => if a == b then [[]] else []
  | Atom.var x, Atom.var y => if x == y then [[]] else [[BindingRel.val x (Atom.var y)]]
  | Atom.var x, r => [[BindingRel.val x r]]
  | l, Atom.var y => [[BindingRel.val y l]]
  | Atom.expr xs, Atom.expr ys => matchAll custom [[]] xs ys
  | l@(Atom.gnd _), r => match custom with | some f => f l r | none => if l == r then [[]] else []
  | l, r@(Atom.gnd _) => match custom with | some f => f r l | none => if l == r then [[]] else []
  | l, r => if l == r then [[]] else []

/-- Pointwise-match two atom lists, threading the consistent binding sets accumulated so far
    (`acc`). Lists of different lengths do not match. -/
def matchAll (custom : Option GroundMatcher) (acc : List Bindings) : List Atom → List Atom → List Bindings
  | [], [] => acc
  | x :: xs, y :: ys =>
      let subs := matchAtomsWith custom x y
      matchAll custom (acc.flatMap (fun a => subs.flatMap (fun b => Bindings.merge a b))) xs ys
  | _, _ => []

end

/-- Match pattern `l` against `r` with the default matcher (no custom grounded matching), returning
    every binding set under which they unify. -/
def matchAtoms (l r : Atom) : List Bindings := matchAtomsWith none l r

/-- Apply a binding set as a substitution. Equality-only relations do not choose an orientation;
    value bindings do. -/
def bindingsToSubst (b : Bindings) : Subst :=
  b.foldr (fun r s => match r with | BindingRel.val x v => (x,v)::s | _ => s) []

/-- Apply a binding set to an atom as a substitution (value bindings only, since `eq` aliases are
    dropped by `bindingsToSubst`). -/
def instantiate (b : Bindings) (a : Atom) : Atom := Subst.apply (bindingsToSubst b) a

end Metta
