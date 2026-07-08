-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILTests.Runtime
Layer: Tests
Purpose: The end-to-end demonstration of the spec-to-runtime: encode a dialect as a MeTTaIL
  presentation (its rewrite rules) and run terms through the verified normalizer `eval`. The dialect is
  the SKI combinatory calculus, the canonical left-normal orthogonal system, so the leftmost-outermost
  strategy of `eval` is normalizing for it. Each reduction is checked at build time with `decide`, so
  these are both regression tests and a demonstration that editing the spec yields a working runtime
  whose every step is proved sound by `eval_sound`.
Imports: MeTTaIL.Semantics.Eval
Trusted boundary: none
Main exports: skiPres (the SKI presentation as a fixture)
Open obligations: none
-/
import MeTTaIL.Runtime.Generic
import MeTTaIL.Semantics.OSLF

namespace MeTTaIL.Tests
open MeTTaIL

/-- Application `(f x)` as a binary constructor. -/
private def app (f x : AST) : AST := .sexp (.id "app") [f, x]
/-- A nullary constructor (a combinator or a constant). -/
private def cst (n : String) : AST := .sexp (.id n) []
/-- A pattern variable in a rewrite left-hand side. -/
private def pv (v : String) : AST := .var (.base v)

private def S : AST := cst "S"
private def K : AST := cst "K"
private def Icomb : AST := cst "I"

/-- The SKI combinatory calculus as a presentation: just its three rewrite rules. The exports, terms,
    and equations are unused by the reducer, so they are empty here; populating `terms` would give the
    generic S-expression front end a symbol table. -/
def skiPres : Presentation :=
  .mk [] [] []
    [ { name := "K", rw := .base (app (app K (pv "x")) (pv "y")) (pv "x") },
      { name := "S", rw := .base (app (app (app S (pv "x")) (pv "y")) (pv "z"))
                                  (app (app (pv "x") (pv "z")) (app (pv "y") (pv "z"))) },
      { name := "I", rw := .base (app Icomb (pv "x")) (pv "x") } ]
    []

-- `I a` returns `a`.
example : (eval skiPres 100 (app Icomb (cst "a")) == cst "a") = true := by decide

-- `K a b` returns `a`.
example : (eval skiPres 100 (app (app K (cst "a")) (cst "b")) == cst "a") = true := by decide

-- `S K K a` reduces to `a`: this is `I = S K K` applied to `a`, the classic derivation.
example : (eval skiPres 100 (app (app (app S K) K) (cst "a")) == cst "a") = true := by decide

-- A larger run: `S K K (S K K a)` reduces to `a` as well.
example :
    (eval skiPres 200 (app (app (app S K) K) (app (app (app S K) K) (cst "a"))) == cst "a") = true := by
  decide

-- The output is a normal form: no further `oneStep` applies to the result.
example : oneStep skiPres (eval skiPres 100 (app (app (app S K) K) (cst "a"))) = none := by decide

-- String front end: type a term, get the answer. `#eval` runs the compiled `run` (parse, normalize,
-- print); the verified core is the AST-level checks above together with `eval_sound`.
#eval run skiPres 100 "(app (app (app S K) K) a)"   -- some "a"
#eval run skiPres 100 "(app (app K a) b)"           -- some "a"
#eval run skiPres 100 "(app I (app (app K a) b))"   -- some "a"

-- A second, unrelated dialect from the same engine: Peano arithmetic. This is the genericity point:
-- only the presentation changes, the verified reducer is reused as is.
private def Z : AST := cst "Z"
private def succ (n : AST) : AST := .sexp (.id "succ") [n]
private def plus (a b : AST) : AST := .sexp (.id "plus") [a, b]
private def num : Nat → AST
  | 0 => Z
  | n + 1 => succ (num n)

/-- Peano addition as a presentation: `plus Z y = y` and `plus (succ x) y = succ (plus x y)`. -/
def natPres : Presentation :=
  .mk [] [] []
    [ { name := "plusZ", rw := .base (plus Z (pv "y")) (pv "y") },
      { name := "plusS", rw := .base (plus (succ (pv "x")) (pv "y"))
                                      (succ (plus (pv "x") (pv "y"))) } ]
    []

-- 2 + 1 = 3.
example : (eval natPres 100 (plus (num 2) (num 1)) == num 3) = true := by decide
-- 3 + 4 = 7.
example : (eval natPres 300 (plus (num 3) (num 4)) == num 7) = true := by decide

#eval run natPres 100 "(plus (succ (succ Z)) (succ Z))"   -- some "(succ (succ (succ Z)))"

/-! ### The compile path: a dialect built through the presentation algebra

The demos above hand a `Presentation` to `run` directly. Here we instead build a `.module`-style theory
instance in the presentation algebra (declare a sort, add the operators, add the rewrite rules), let
`elaborate` compile it to a `Presentation`, and run terms with `runInst`. Changing the theory instance
changes the runtime: this is the "tweak the LanguageDef, get a runtime" path end to end. -/

/-- The single sort of the toy boolean dialect. -/
private def tmCat : Cat := .idCat "Tm"

/-- A constructor rule of the toy dialect: a label producing the sort `Tm`. -/
private def tmRule (n : String) (items : List Item) : Rule :=
  { label := .id n, cat := tmCat, items := items }

/-- The constructors and the two negation rewrites, shared between the theory instance and the
    presentation it should compile to. -/
private def boolTerms : List Rule :=
  [tmRule "tt" [], tmRule "ff" [], tmRule "notOp" [.nterminal tmCat]]

private def rwNotTt : RewriteDecl :=
  { name := "notTt", rw := .base (.sexp (.id "notOp") [.sexp (.id "tt") []]) (.sexp (.id "ff") []) }
private def rwNotFf : RewriteDecl :=
  { name := "notFf", rw := .base (.sexp (.id "notOp") [.sexp (.id "ff") []]) (.sexp (.id "tt") []) }

/-- Booleans with negation, as a theory instance: export `Tm`, add the constructors, then the rewrites. -/
private def boolInst : TheoryInst :=
  .addRewrites (.addTerms (.addExports .empty [.base tmCat]) boolTerms) [rwNotTt, rwNotFf]

/-- The presentation `boolInst` should elaborate to. -/
private def boolPres : Presentation := .mk [tmCat] boolTerms [] [rwNotTt, rwNotFf] []

-- The theory instance compiles to the expected presentation.
example : ((elaborate {} boolInst).toOption == some boolPres) = true := by decide
-- The compiled presentation negates at the AST level: `(notOp tt)` reduces to `ff`.
example : (eval boolPres 100 (.sexp (.id "notOp") [.sexp (.id "tt") []]) == .sexp (.id "ff") []) = true := by
  decide
-- End to end through the string front end with `runInst` (elaborate then run).
#eval runInst {} boolInst 100 "(notOp tt)"   -- Except.ok (some "ff")
#eval runInst {} boolInst 100 "(notOp ff)"   -- Except.ok (some "tt")

/-! ### OSLF: the identity combinator inhabits the arrow type `A → A`

The spatial-behavioral logic (`MeTTaIL.Semantics.OSLF`) reads the function arrow as the possibly modal
operator over the application context (Stay-Meredith). Concretely, in SKI the identity combinator `I`
has type `A → A` for every property `A`: applied to any `u` of type `A`, `(app I u)` reduces by the ι
rule to `u`, which is of type `A`. So the derived arrow type is inhabited, and the modal reading is the
operational one. -/
example (A : OSLF.Pred) : OSLF.Pred.arrow skiPres (.id "app") A A Icomb := by
  intro u hu
  exact ⟨u, RewStepMany.single (oneStep_sound skiPres (app Icomb u) rfl), hu⟩

end MeTTaIL.Tests
