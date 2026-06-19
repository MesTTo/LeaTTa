/-
LeaTTa: Chapter: The Gradual Type System.
-/
import VersoManual
import Illuminate
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The Gradual Type System" =>
%%%
tag := "sec-types"
%%%

MeTTa is *gradually* typed {citep siekTaha}[]: a declared arrow signature `(: op (-> T₁ … Tₙ R))`
triggers argument checking, an undeclared operator is left unchecked, and the special types
`%Undefined%` (the dynamic type) and `Atom` (the top meta-type) are compatible with everything.
LeaTTa formalizes this discipline operationally through `getTypes`, `matchType`, `typeCheckArgs`, and
`typeMismatch` in `Minimal/Interpreter.lean`, and proves its key properties.

# Type Compatibility Is *Consistency*, Not Equality

The relation deciding whether an actual type may be supplied where a parameter type is expected is
Siek and Taha's *consistency* `~`. It is *reflexive and symmetric but _not_ transitive*: routing
through the dynamic type would otherwise relate *all* types and make the discipline vacuous. The
following is a self-contained, fully checked rendering of that result (the development also proves it
for the real `matchType`):

```lean
/-- A miniature type language: named types plus the two gradual wildcards. -/
inductive Ty where
  | sym (name : String)
  | undef   -- %Undefined%, the dynamic type
  | top     -- Atom, the top meta-type

/-- Consistency: equal types are consistent, and each wildcard is consistent with anything. -/
inductive Consistent : Ty → Ty → Prop where
  | same   (t : Ty) : Consistent t t
  | undefL (t : Ty) : Consistent .undef t
  | undefR (t : Ty) : Consistent t .undef
  | topL   (t : Ty) : Consistent .top t
  | topR   (t : Ty) : Consistent t .top

/-- Two distinct named types are not consistent (no wildcard rule applies). -/
theorem not_consistent_distinct {a b : String} (hab : a ≠ b) :
    ¬ Consistent (.sym a) (.sym b) := by
  intro h; cases h with | same => exact hab rfl

/-- *The gradual hallmark: consistency is not transitive.*
`Number ~ %Undefined% ~ String`, yet `Number ≁ String`. -/
theorem consistent_not_transitive :
    ¬ ∀ x y z, Consistent x y → Consistent y z → Consistent x z := by
  intro h
  exact not_consistent_distinct (a := "Number") (b := "String") (by decide)
    (h _ .undef _ (.undefR _) (.undefL _))
```

Compatibility is a *tolerance* relation, not a preorder. That is what keeps the `%Undefined%`/`Atom`
escape hatch sound without collapsing the type discipline. `Gradual.lean` proves `Consistent.refl`,
`Consistent.symm`, and `Consistent.not_transitive` for the full `Atom` type, and
`matchType_not_transitive` shows the *executable* matcher inherits the property.

# What the Type System Guarantees

For MeTTa's intended on-chain use, a well-typed program must never be rejected spuriously, and a
reported type error must be faithful. LeaTTa proves both against the real kernel functions:

 * *Permissiveness*: undeclared operators, arguments beyond the declared arity, and the
   `%Undefined%`/`Atom` wildcards are never rejected (`typeMismatch_undeclared`,
   `typeCheckArgs_no_param`, `matchType_undefined_left`/`right`, `matchType_atom_left`/`right`).
 * *Totality*: `getTypes` assigns every atom at least one type (`getTypes_ne_nil`): gradual
   typing has no "untyped gap".
 * *Faithful errors*: when the checker flags a mismatch at position `pos`, one evaluation step
   returns *exactly* the corresponding `(Error … (BadArgType pos expected actual))`
   (`mettaEval_badArgType`), and the reported `actual` is a genuine type of the offending argument
   (`typeCheckArgs_act_real`); never fabricated.
 * *Grounded-core preservation*: arithmetic is closed on `Number`, comparison and `==` yield
   `Bool` or faithfully propagate an error (`numBin_isNumber`, `numCmp_isBool`,
   `eqAtom_isBoolOrError`).

The `matchType` matcher treats `Atom` as a wildcard on *either* side. This matches both Hyperon's
Rust implementation (`interpreter.rs`) and the prealpha specification; the point was not documented
before LeaTTa. Casting between types is the standard-library `type-cast`, which checks an atom's
actual types against a target and returns the atom or `(Error atom BadType)`.
