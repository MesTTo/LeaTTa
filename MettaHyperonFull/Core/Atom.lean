/-
Module: MettaHyperonFull.Core.Atom
Layer: Core
Purpose: The core MeTTa atom datatype and the values it carries. Defines symbols, variables, grounded
  payloads, and expressions, together with structural equality, the syntactic meta-types, the built-in
  type designators, the arrow constructor, and basic measures over atoms. Structural equality is
  hand-written so it reduces definitionally for the metatheory layer.
Imports: (none beyond core)
Trusted boundary: none
Main exports: VarName, Ground, Atom, Atom.beq, Atom.beqList, the BEq Atom instance, MetaType,
  ReduceResult, the built-in type-designator atoms, Atom.isError, Atom.metaType,
  Atom.typeAtomOfMetaType, Atom.isBuiltinTypeSymbol, Atom.mkArrow, Atom.isArrow, Atom.head?,
  Atom.args?, Atom.size, Atom.vars
Open obligations: none
-/
namespace Metta

/-- Names of MeTTa variables, without the leading `$`. -/
abbrev VarName := String

/-- Grounded payloads implemented directly by the Lean runtime. Use `external tag payload`
    for host-language values whose semantics lies outside this interpreter. -/
inductive Ground where
  | int : Int → Ground
  | float : Float → Ground
  | str : String → Ground
  | bool : Bool → Ground
  | unit : Ground
  | error : String → Ground
  | external : String → String → Ground
  deriving Repr, BEq, Inhabited

/-- MeTTa atoms: symbols, variables, grounded atoms, and expressions. -/
inductive Atom where
  | sym : String → Atom
  | var : VarName → Atom
  | gnd : Ground → Atom
  | expr : List Atom → Atom
  deriving Repr, Inhabited

mutual
/-- Structural Boolean equality on atoms. Hand-written rather than `deriving BEq` so that it
    *reduces* definitionally: `deriving BEq` for this nested inductive (`expr : List Atom`)
    compiles to well-founded recursion that is opaque to `rfl`/`simp`/`decide`, so it will not even
    reduce on a constructor mismatch, which blocks all equational reasoning about the matcher in
    the metatheory layer. This structural version is kernel-reducible and computes exactly the same
    result the derived instance would. (`gnd` payloads still defer to `Ground`'s `BEq`, i.e. IEEE
    float equality, so the documented host-float behaviour is unchanged.) -/
def Atom.beq : Atom → Atom → Bool
  | Atom.sym a, Atom.sym b => a == b
  | Atom.var a, Atom.var b => a == b
  | Atom.gnd a, Atom.gnd b => a == b
  | Atom.expr a, Atom.expr b => Atom.beqList a b
  | _, _ => false
/-- Pointwise structural equality of atom lists (companion to `Atom.beq`). -/
def Atom.beqList : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => Atom.beq x y && Atom.beqList xs ys
  | _, _ => false
end

instance : BEq Atom := ⟨Atom.beq⟩

/-- Coarse meta-types from the current Hyperon specification. -/
inductive MetaType where
  | atom | symbol | variable | expression | grounded | typeType | undefined | errorType
  deriving Repr, BEq, Inhabited

/-- Runtime outcomes returned by grounded operations. -/
inductive ReduceResult where
  | ok : List Atom → ReduceResult
  | noReduce : ReduceResult
  | incorrectArgument : String → ReduceResult
  | runtimeError : String → ReduceResult
  deriving Repr, BEq, Inhabited

namespace Atom

/-- The unit atom `()`: the grounded `Unit`. An assertion succeeds by reducing to it. -/
def unit : Atom := Atom.gnd Ground.unit
/-- The Boolean `True` as a grounded atom. -/
def trueA : Atom := Atom.gnd (Ground.bool true)
/-- The Boolean `False` as a grounded atom. -/
def falseA : Atom := Atom.gnd (Ground.bool false)
/-- The `Empty` symbol: reducing to it prunes the current nondeterministic branch (no results). -/
def empty : Atom := Atom.sym "Empty"
/-- The `NotReducible` marker: a redex that yielded no reduction. -/
def notReducible : Atom := Atom.sym "NotReducible"
/-- The gradual top type `%Undefined%`, compatible with every type on either side of a check. -/
def undefined : Atom := Atom.sym "%Undefined%"
/-- The kind of types, `Type`. -/
def typeSym : Atom := Atom.sym "Type"
/-- The `Atom` meta-type: accepts anything, so quoted/unevaluated arguments stay well-typed. -/
def atomType : Atom := Atom.sym "Atom"
def symbolType : Atom := Atom.sym "Symbol"
def variableType : Atom := Atom.sym "Variable"
def expressionType : Atom := Atom.sym "Expression"
/-- The `Grounded` meta-type (numbers, booleans, grounded operations). -/
def groundedType : Atom := Atom.sym "Grounded"
/-- The `ErrorType` symbol: the type of `(Error …)` atoms. -/
def errorType : Atom := Atom.sym "ErrorType"

/-- True if `a` is an error atom: either `(Error … …)` or a grounded `Ground.error`. -/
def isError : Atom → Bool
  | Atom.expr [Atom.sym "Error", _, _] => true
  | Atom.gnd (Ground.error _) => true
  | _ => false

/-- The syntactic meta-type (kind) of an atom: symbol / variable / grounded / expression, with the
    reserved symbols `Type` and `ErrorType` recognised specially. -/
def metaType : Atom → MetaType
  | Atom.sym "Type" => MetaType.typeType
  | Atom.sym "ErrorType" => MetaType.errorType
  | Atom.sym _ => MetaType.symbol
  | Atom.var _ => MetaType.variable
  | Atom.gnd _ => MetaType.grounded
  | Atom.expr _ => MetaType.expression

/-- The type designator atom for a meta-type (inverse of `metaType` on the built-in type symbols). -/
def typeAtomOfMetaType : MetaType → Atom
  | MetaType.atom => atomType
  | MetaType.symbol => symbolType
  | MetaType.variable => variableType
  | MetaType.expression => expressionType
  | MetaType.grounded => groundedType
  | MetaType.typeType => typeSym
  | MetaType.undefined => undefined
  | MetaType.errorType => errorType

/-- True if `a` is exactly one of the special built-in type designators. -/
def isBuiltinTypeSymbol : Atom → Bool
  | Atom.sym "Type" => true
  | Atom.sym "%Undefined%" => true
  | Atom.sym "Atom" => true
  | Atom.sym "Symbol" => true
  | Atom.sym "Variable" => true
  | Atom.sym "Expression" => true
  | Atom.sym "Grounded" => true
  | Atom.sym "ErrorType" => true
  | _ => false

/-- Function type constructor: `(-> A B C)`. -/
def mkArrow (args : List Atom) (ret : Atom) : Atom := Atom.expr (Atom.sym "->" :: (args ++ [ret]))

def isArrow : Atom → Bool
  | Atom.expr (Atom.sym "->" :: _) => true
  | _ => false

/-- The head (first child) of an expression, or `none` for a non-expression / empty expression. -/
def head? : Atom → Option Atom
  | Atom.expr (x :: _) => some x
  | _ => none

/-- The argument list (children after the head) of an expression, or `none` otherwise. -/
def args? : Atom → Option (List Atom)
  | Atom.expr (_ :: xs) => some xs
  | _ => none

/-- Structural size: leaves count 1, an expression is `1 +` the sizes of its children. Used as the
    well-founded measure for recursion/termination over atoms. -/
def size : Atom → Nat
  | Atom.sym _ => 1
  | Atom.var _ => 1
  | Atom.gnd _ => 1
  | Atom.expr xs => 1 + (xs.map size).sum

/-- All variable occurrences in `a`, left-to-right with duplicates. Atoms have no binders, so
    every occurrence is free; see `FreeVars.lean` for the named notion used in the metatheory. -/
def vars : Atom → List VarName
  | Atom.var x => [x]
  | Atom.expr xs => (xs.map vars).flatten
  | _ => []

end Atom
end Metta
