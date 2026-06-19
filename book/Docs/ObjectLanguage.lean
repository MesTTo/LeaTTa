/-
LeaTTa: Chapter: The Object Language.
-/
import VersoManual
import Illuminate
import Docs.Cd
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The Object Language: Atoms" =>
%%%
tag := "sec-atoms"
%%%

Everything in MeTTa, whether programs, data, types, or the rewrite rules that drive evaluation, is an
*atom*. LeaTTa's object language is a single inductive type with four constructors, mirroring
MeTTa's four *metatypes*. The definitions in this chapter are self-contained and are elaborated by
Lean as you read them; the full development uses exactly these shapes.

# Grounded Values and Atoms

A *grounded* value is the primitive host-language data an atom may carry; numbers, strings,
Booleans, the unit value, and error payloads:

```lean
/-- A grounded value: the primitive data a MeTTa atom can carry. -/
inductive Ground where
  | int   : Int → Ground
  | float : Float → Ground
  | str   : String → Ground
  | bool  : Bool → Ground
  | unit  : Ground
  | error : String → Ground
deriving Repr, Inhabited
```

An *atom* is then a symbol, a variable, a grounded value, or an expression (a list of atoms):

```lean
/-- MeTTa atoms: the four metatypes; `Symbol`, `Variable`, `Grounded`, and `Expression`. -/
inductive Atom where
  | sym  : String → Atom
  | var  : String → Atom
  | gnd  : Ground → Atom
  | expr : List Atom → Atom
deriving Inhabited
```

The four metatypes drive evaluation order and matching: a {lean}`Atom.sym` is an opaque identifier
(a function name, a type name, a constructor); a {lean}`Atom.var` is a unification variable; a
{lean}`Atom.gnd` carries host data; and an {lean}`Atom.expr` is an application or a tuple. The empty
expression {lean}`Atom.expr []` is MeTTa's unit value `()`.

# Structural Equality, and Why It Is Hand-Written

Matching, indexing, and the proofs about them all need a *decidable, kernel-reducible* equality on
atoms. LeaTTa uses a *hand-written* structural `BEq Atom` rather than the one `deriving BEq` would
generate, because the derived instance is compiled to opaque well-founded recursion that neither
`decide` nor `rfl` can unfold, which would block every matcher proof. The hand-written instance
reduces definitionally, so facts like "a symbol never equals an expression" hold by `rfl`.

:::paragraph
There is one subtlety, and LeaTTa is candid about it. `Atom` does _not_ admit a lawful `BEq`
instance, because IEEE-754 floating point breaks the laws: the grounded atoms `0.0` and `-0.0`
compare *equal* yet are distinct, and `NaN` is *not* equal to itself, so reflexivity fails.
Consequently `LawfulBEq Atom` is _false_, and no theorem in LeaTTa may assume it. Equality up to a
consistent renaming of variables, namely *α-equivalence*, is therefore given its own decided relation,
and the proofs about it carefully avoid the float pitfall. This honesty about the foundations is the
kind of detail a verified language definition must get right.
:::

# Metatypes at a Glance

The metatype of an atom is read off its constructor, and the special type symbols `%Undefined%`
(the dynamic/unknown type) and `Atom` (the top meta-type, which matches anything) sit above the
ordinary types in the gradual hierarchy used by the type system ({ref "sec-types"}[the next
chapters build on this]):

```diagram (cssWidth := "36em")
cd do
  let top ← CDM.node "Atom / %Undefined%" cdPurple
  let s ← CDM.node "Symbol" cdInk
  let v ← CDM.node "Variable" cdInk
  let g ← CDM.node "Grounded" cdInk
  let e ← CDM.node "Expression" cdInk
  CDM.grid #[#[some top], #[some s, some v, some g, some e]]
  CDM.arrow s top none cdBlue
  CDM.arrow v top none cdBlue
  CDM.arrow g top none cdBlue
  CDM.arrow e top none cdBlue
```
