/-
Module: MettaHyperonFull.Core.Types
Layer: Core
Purpose: The type environment read from a space and the typing it supports. Collects `(: a t)`
  assignments and `(<: a b)` subtypings, computes the declared types of an atom, decides fuel-bounded
  subtyping (with the gradual top and bottom types on either side), and splits arrow types. Also gives
  the declarative typing judgement the metatheory uses. Runtime type checking is control-sensitive and
  is modelled separately in the interpreter and TypeSoundness proofs.
Imports: MettaHyperonFull.Core.Space
Trusted boundary: none
Main exports: TypeEnv, TypeEnv.empty, TypeEnv.fromSpace, TypeEnv.typesOf, TypeEnv.inheritsFuel,
  TypeEnv.inherits, TypeEnv.matchTypes, TypeEnv.arrowParts?, HasType
Open obligations: subtyping is fuel-bounded, with `inherits` using a depth budget of 64, so very deep
  inheritance chains are not followed past that bound.
-/
import MettaHyperonFull.Core.Space

namespace Metta

/-- Type environment extracted from a MeTTa space. -/
structure TypeEnv where
  /-- Type assignments `(: a t)` of the space, as `(a, t)` pairs. -/
  assignments : List (Atom × Atom)
  /-- Subtyping declarations `(<: a b)` of the space, as `(a, b)` pairs. -/
  inheritance : List (Atom × Atom)
  deriving BEq, Inhabited

namespace TypeEnv

def empty : TypeEnv := ⟨[], []⟩

/-- Extract a `TypeEnv` from a space: collect `(: a t)` assignments and `(<: a b)` subtypings. -/
def fromSpace (s : Space) : TypeEnv :=
  let asg := s.atoms.filterMap (fun x => match x with
    | Atom.expr [Atom.sym ":", a, t] => some (a,t)
    | _ => none)
  let inh := s.atoms.filterMap (fun x => match x with
    | Atom.expr [Atom.sym "<:", a, b] => some (a,b)
    | _ => none)
  ⟨asg, inh⟩

/-- The declared types of `a`: its metatype plus every `t` with `(: a t)` in the environment. -/
def typesOf (env : TypeEnv) (a : Atom) : List Atom :=
  let metaTy := Atom.typeAtomOfMetaType (Atom.metaType a)
  metaTy :: (env.assignments.filterMap (fun p => if p.fst == a then some p.snd else none))

/-- Fuel-bounded subtyping `a <: b`: reflexivity, the universal supertypes `Atom`/`%Undefined%`, and
    transitive closure of the declared `(<: …)` edges (the `fuel` bounds the inheritance-chain depth). -/
def inheritsFuel : Nat → TypeEnv → Atom → Atom → Bool
  | 0, _, a, b => a == b || b == Atom.atomType || b == Atom.undefined
  | Nat.succ n, env, a, b =>
      a == b || b == Atom.atomType || b == Atom.undefined ||
      env.inheritance.any (fun p => p.fst == a && (p.snd == b || inheritsFuel n env p.snd b))

/-- Subtyping `a <: b` (`inheritsFuel` with a depth budget of 64). -/
def inherits (env : TypeEnv) (a b : Atom) : Bool := inheritsFuel 64 env a b

/-- Whether `actual` is acceptable where `expected` is wanted: gradual top/bottom (`Atom`,
    `%Undefined%`) on either side, or `actual <: expected`. -/
def matchTypes (env : TypeEnv) (actual expected : Atom) : Bool :=
  expected == Atom.undefined || expected == Atom.atomType || actual == Atom.undefined || inherits env actual expected

/-- Split `(-> A1 ... An R)` into argument types and return type. -/
def arrowParts? : Atom → Option (List Atom × Atom)
  | Atom.expr (Atom.sym "->" :: xs) => match xs.reverse with
      | ret :: revArgs => some (revArgs.reverse, ret)
      | [] => none
  | _ => none

end TypeEnv

/-- The declarative typing judgement `a : t` used by the metatheory: an atom has its meta-type, any
    `:`-assigned type, and any supertype under `inherits`. Runtime type *checking* is control-sensitive
    and is modelled separately and faithfully by `Interpreter.typeMismatch` (see
    `Proofs/TypeSoundness.lean`); this relation is the static discipline the preservation proofs use. -/
inductive HasType (env : TypeEnv) : Atom → Atom → Prop where
  | metaTy (a : Atom) : HasType env a (Atom.typeAtomOfMetaType (Atom.metaType a))
  | assigned (a t : Atom) : (a,t) ∈ env.assignments → HasType env a t
  | subtype (a t u : Atom) : HasType env a t → TypeEnv.inherits env t u = true → HasType env a u

end Metta
