-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

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

Everything in MeTTa is an *atom*. Programs, data, types, and the rewrite rules that drive evaluation
are all atoms, and there are only four kinds of them. In LeaTTa the object language is one Lean
inductive type with a constructor for each kind, which are MeTTa's four *metatypes*. The definitions
you see here are the real ones: Lean elaborates them as you read, and the rest of the development is
built on exactly these shapes. Let us start with the data an atom can carry.

# Grounded Values and Atoms

A *grounded* value is the primitive host-language data an atom can hold: a number, a string, a
Boolean, the unit value, an error payload, or a value from outside the interpreter held behind an
`external` tag:

```lean
/-- A grounded value: the primitive data a MeTTa atom can carry. -/
inductive Ground where
  | int   : Int → Ground
  | float : Float → Ground
  | str   : String → Ground
  | bool  : Bool → Ground
  | unit  : Ground
  | error : String → Ground
  | external : String → String → Ground
deriving Repr, Inhabited
```

So `1`, `1.05`, and `True` all become grounded atoms, and `external` is the escape hatch for host
values whose meaning lives outside MeTTa.

An *atom* is then a symbol, a variable, a grounded value, or an expression, which is just a list of
atoms:

```lean
/-- MeTTa atoms: the four metatypes; `Symbol`, `Variable`, `Grounded`, and `Expression`. -/
inductive Atom where
  | sym  : String → Atom
  | var  : String → Atom
  | gnd  : Ground → Atom
  | expr : List Atom → Atom
deriving Inhabited
```

These four constructors are MeTTa's metatypes, and they decide how evaluation and matching treat an
atom:

 * a {lean}`Atom.sym` is an opaque identifier, like a function name, a type name, or a constructor;
 * a {lean}`Atom.var` is a unification variable, written `$x` in surface syntax;
 * a {lean}`Atom.gnd` carries host data, the grounded values above;
 * an {lean}`Atom.expr` is an application or a tuple, a list of atoms.

The empty expression {lean}`Atom.expr []` is MeTTa's unit value `()`.

# When Are Two Atoms Equal?

Matching, indexing, and the proofs about them all compare atoms, and they need a comparison the Lean
kernel can both *compute* and *reason about*. So LeaTTa writes the structural `BEq Atom` by hand
rather than taking the one `deriving BEq` would generate. The derived instance compiles to opaque
well-founded recursion that neither `decide` nor `rfl` can unfold, which would block every matcher
proof. The hand-written instance reduces definitionally, so a fact like "a symbol never equals an
expression" holds by `rfl`.

:::paragraph
There is one honest catch. `Atom` does _not_ admit a lawful `BEq` instance, because IEEE-754 floating
point breaks the laws:
the grounded atoms `0.0` and `-0.0` compare *equal* yet are distinct, and `NaN` is *not* equal to
itself, so reflexivity fails. Consequently `LawfulBEq Atom` is _false_, and no theorem in LeaTTa
may assume it. Equality up to a consistent renaming of variables, namely *α-equivalence*, is
therefore given its own decided relation, and the proofs about it carefully avoid the float pitfall.
:::

# Metatypes at a Glance

The metatype of an atom is read off its constructor. The special type symbols `%Undefined%`
(the dynamic/unknown type) and `Atom` (the top meta-type, which matches anything) sit above the
ordinary types in the gradual hierarchy used by the type system ({ref "sec-types"}[covered in the
type system chapter]):

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
