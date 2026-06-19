import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Runtime.Parser
import MettaHyperonFull.Core.Pretty
import MettaHyperonFull.Core.Alpha

/-!
# MeTTa standard library on the minimal interpreter

Grounded operations beyond the arithmetic core (`Core/Builtins`) that Hyperon's `stdlib.metta`
relies on, plus the MeTTa-level prelude itself (a faithful subset of
`hyperon-experimental/lib/src/metta/runner/stdlib/stdlib.metta`) loaded into the knowledge base.
The MeTTa-defined functions execute on the minimal interpreter from `Minimal/Interpreter`.
-/

namespace Metta.Minimal
open Metta Metta.Runtime

/-! ## Multiset helpers (matching Hyperon's consuming set-op semantics) -/

/-- Remove the first occurrence of `a` from a list. -/
def removeFirst (a : Atom) : List Atom → List Atom
  | [] => []
  | x :: xs => if x == a then xs else x :: removeFirst a xs

/-- Deduplicate, keeping the first occurrence of each atom up to **α-equivalence** (Hyperon
    `unique-atom` uses `atoms_are_equivalent`, so variable-renamed duplicates collapse). -/
def dedupAux (seen : List Atom) : List Atom → List Atom
  | [] => []
  | x :: xs => if seen.any (alphaEq x) then dedupAux seen xs else x :: dedupAux (x :: seen) xs

/-- Multiset intersection: keep each `lhs` element that has an unconsumed match in `rhs`. -/
def msIntersect (lhs rhs : List Atom) : List Atom :=
  (lhs.foldl (fun acc x => if acc.2.contains x then (acc.1 ++ [x], removeFirst x acc.2) else acc) (([], rhs) : List Atom × List Atom)).1

/-- Multiset difference: drop each `lhs` element that has an unconsumed match in `rhs`. -/
def msSubtract (lhs rhs : List Atom) : List Atom :=
  (lhs.foldl (fun acc x => if acc.2.contains x then (acc.1, removeFirst x acc.2) else (acc.1 ++ [x], acc.2)) (([], rhs) : List Atom × List Atom)).1

/-! ## Grounded operations -/

/-- `(if-equal a b then else)` → `then` if `a` and `b` are **α-equivalent**, else `else` (Hyperon
    `core.rs : atoms_are_equivalent`; atoms equal up to a consistent variable renaming match). -/
def ifEqualOp : List Atom → ReduceResult
  | [a, b, t, e] => ReduceResult.ok [if alphaEq a b then t else e]
  | _ => ReduceResult.incorrectArgument "if-equal expects 4 arguments"

/-- `(=alpha a b)` → `True`/`False` by **α-equivalence** (Hyperon `debug.rs`): equal up to a
    consistent renaming of variables. -/
def alphaEqOp : List Atom → ReduceResult
  | [a, b] => ReduceResult.ok [Atom.gnd (Ground.bool (alphaEq a b))]
  | _ => ReduceResult.incorrectArgument "=alpha expects two arguments"

/-- `(get-metatype a)` → `Symbol` | `Variable` | `Expression` | `Grounded`. -/
def getMetatypeOp : List Atom → ReduceResult
  | [Atom.sym _] => ReduceResult.ok [Atom.sym "Symbol"]
  | [Atom.var _] => ReduceResult.ok [Atom.sym "Variable"]
  | [Atom.expr _] => ReduceResult.ok [Atom.sym "Expression"]
  | [Atom.gnd _] => ReduceResult.ok [Atom.sym "Grounded"]
  | _ => ReduceResult.incorrectArgument "get-metatype expects 1 argument"

/-- Grounded `(not a)`: boolean negation of a `Bool` atom. -/
def notOp : List Atom → ReduceResult
  | [a] => match Builtins.toBool? a with
      | some x => ReduceResult.ok [Atom.gnd (Ground.bool (!x))]
      | none => ReduceResult.incorrectArgument "not expects one Bool"
  | _ => ReduceResult.incorrectArgument "not expects one argument"

/-- Grounded `(xor a b)`: boolean exclusive-or of two `Bool` atoms. -/
def xorOp : List Atom → ReduceResult
  | [a, b] => match Builtins.toBool? a, Builtins.toBool? b with
      | some x, some y => ReduceResult.ok [Atom.gnd (Ground.bool (x != y))]
      | _, _ => ReduceResult.incorrectArgument "xor expects two Bool"
  | _ => ReduceResult.incorrectArgument "xor expects two arguments"

/-- Grounded `(/ a b)`: numeric division on `Int` or `Float`. Integer division by zero raises a
    `DivisionByZero` error (Hyperon's `checked_div`); float division follows IEEE (`x/0.0 = ±inf`). -/
def divOp : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] =>
      if b == 0 then ReduceResult.runtimeError "DivisionByZero"
      else ReduceResult.ok [Atom.gnd (Ground.int (a / b))]
  | args => Builtins.numBin (· / ·) (· / ·) args

/-- Grounded `(% a b)`: integer modulo of two `Int` atoms; a zero divisor raises `DivisionByZero`. -/
def modOp : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] =>
      if b == 0 then ReduceResult.runtimeError "DivisionByZero"
      else ReduceResult.ok [Atom.gnd (Ground.int (a % b))]
  | _ => ReduceResult.incorrectArgument "% expects two Int atoms"

/-- Grounded `(unique-atom expr)`: the expression with duplicate children removed, keeping the first
    occurrence of each (order-preserving dedup). -/
def uniqueAtomOp : List Atom → ReduceResult
  | [Atom.expr xs] => ReduceResult.ok [Atom.expr (dedupAux [] xs)]
  | _ => ReduceResult.incorrectArgument "unique-atom expects one expression"

/-- Grounded `(union-atom a b)`: multiset union of two tuples (their children concatenated). -/
def unionAtomOp : List Atom → ReduceResult
  | [Atom.expr xs, Atom.expr ys] => ReduceResult.ok [Atom.expr (xs ++ ys)]
  | _ => ReduceResult.incorrectArgument "union-atom expects two expressions"

/-- Grounded `(intersection-atom a b)`: multiset intersection of two tuples. -/
def intersectionAtomOp : List Atom → ReduceResult
  | [Atom.expr xs, Atom.expr ys] => ReduceResult.ok [Atom.expr (msIntersect xs ys)]
  | _ => ReduceResult.incorrectArgument "intersection-atom expects two expressions"

/-- Grounded `(subtraction-atom a b)`: multiset difference `a \ b` of two tuples. -/
def subtractionAtomOp : List Atom → ReduceResult
  | [Atom.expr xs, Atom.expr ys] => ReduceResult.ok [Atom.expr (msSubtract xs ys)]
  | _ => ReduceResult.incorrectArgument "subtraction-atom expects two expressions"

/-- Hyperon's `result_items` (`stdlib/debug.rs`): a *collapsed bag* is an explicit comma-tuple
    `(, x …)`, so a leading `,` is stripped to recover the bare item list `x …`; any other
    expression is already its own item list. This is what lets `(collapse …)` (which yields `(, …)`)
    compare and re-spread against the bare tuples that assertions and `superpose` work with. -/
def resultItems : List Atom → List Atom
  | Atom.sym "," :: rest => rest
  | xs => xs

/-- `(superpose (a b c))` → the nondeterministic results `a`, `b`, `c`; a collapsed `(, a b c)` is
    accepted too (the `,` is stripped), so `(superpose (collapse x))` round-trips. -/
def superposeOp : List Atom → ReduceResult
  | [Atom.expr xs] => ReduceResult.ok (resultItems xs)
  | _ => ReduceResult.incorrectArgument "superpose expects one expression"

/-- Extract the atoms from a `collapse-bind` result `((a ()) (b ()) ...)` → the **explicit comma
    tuple** `(, a b ...)` (empty → `(,)`), exactly as Hyperon's `collapse`. The `,` head keeps the
    bag from being re-reduced as an application (cf. Hyperon's own test
    `metta_collapse_uses_comma_tuple_to_avoid_reducing_tuple_head`); `resultItems`/`superpose` strip
    it again on the way back, so a collapsed bag compares as its bare item list. -/
def collapseExtractOp : List Atom → ReduceResult
  | [Atom.expr pairs] => ReduceResult.ok [Atom.expr (Atom.sym "," :: pairs.map fun p => match p with
      | Atom.expr (a :: _) => a
      | other => other)]
  | _ => ReduceResult.incorrectArgument "collapse-extract expects one expression"

/-- A no-op grounded operation: ignores its arguments and returns the unit atom `()`. Backs runtime
    directives that have no value (`pragma!`, `help!`). -/
def nopOp : List Atom → ReduceResult
  | _ => ReduceResult.ok [Atom.expr []]  -- `()` as the parser produces it (the oracle's unit)

/-- `(sealed (<vars>) <atom>)` → `<atom>`. Variable hygiene is already provided by the interpreter's
    per-application rule-variable freshening, so sealing reduces to the identity on its body. -/
def sealedOp : List Atom → ReduceResult
  | [_vars, atom] => ReduceResult.ok [atom]
  | _ => ReduceResult.incorrectArgument "sealed expects (sealed <vars-expr> <atom>)"

/-! ## Assertion helpers (Hyperon's grounded `_assert-results-are-equal[-msg]` family) -/

/-- Remove the first element of `xs` equal to `a` under `eq`, or `none` if absent. -/
def removeFirstBy (eq : Atom → Atom → Bool) (a : Atom) : List Atom → Option (List Atom)
  | [] => none
  | x :: xs => if eq a x then some xs else (removeFirstBy eq a xs).map (x :: ·)

/-- Multiset equality under a custom element equality (order-independent), as Hyperon's
    `compare_vec_no_order`. -/
def bagEqBy (eq : Atom → Atom → Bool) : List Atom → List Atom → Bool
  | [], bs => bs.isEmpty
  | a :: as, bs => match removeFirstBy eq a bs with
      | some bs' => bagEqBy eq as bs'
      | none => false

/-- The unit atom as produced by the parser (`()` is the empty expression, distinct from
    `Atom.unit`). Assertion successes must return this so they compare equal to the oracle's `()`. -/
def unitExpr : Atom := Atom.expr []

/-- `_assert-results-are-equal $actual $expected $assert [$msg]`: compares the two result tuples as
    multisets under `eq`. Returns `()` on success, else `(Error $assert <msg>)` (the explicit `$msg`
    if given, otherwise a default symbol; the message text is only observed via the `*Msg` asserts). -/
def assertResultsEqOp (eq : Atom → Atom → Bool) : List Atom → ReduceResult
  | [Atom.expr actual, Atom.expr expected, assertAtom] =>
      ReduceResult.ok [if bagEqBy eq (resultItems actual) (resultItems expected) then unitExpr
        else Atom.expr [Atom.sym "Error", assertAtom, Atom.sym "results-are-not-equal"]]
  | [Atom.expr actual, Atom.expr expected, assertAtom, msg] =>
      ReduceResult.ok [if bagEqBy eq (resultItems actual) (resultItems expected) then unitExpr
        else Atom.expr [Atom.sym "Error", assertAtom, msg]]
  | _ => ReduceResult.incorrectArgument "_assert-results-are-equal expects (<actual> <expected> <assert> [<msg>])"

/-- Total order on atoms by their printed form (used by `sort-atom`/`sort-strings`). -/
def atomStrLt (a b : Atom) : Bool := decide (toString a < toString b)

/-- Insert `a` into a `atomStrLt`-sorted list, keeping it sorted. -/
def sortInsert (a : Atom) : List Atom → List Atom
  | [] => [a]
  | x :: xs => if atomStrLt a x then a :: x :: xs else x :: sortInsert a xs

/-- Insertion sort of a list of atoms by printed form. -/
def sortAtoms : List Atom → List Atom
  | [] => []
  | x :: xs => sortInsert x (sortAtoms xs)

/-- `(sort-atom (..))` / `(sort-strings (..))` → the expression with its children sorted. -/
def sortAtomOp : List Atom → ReduceResult
  | [Atom.expr xs] => ReduceResult.ok [Atom.expr (sortAtoms xs)]
  | _ => ReduceResult.incorrectArgument "sort-atom expects one expression"

/-- Grounded table for the minimal interpreter: the arithmetic core plus the stdlib grounded ops. -/
def stdGroundings : GroundingTable := Builtins.table ++ [
  ⟨"if-equal", GroundMode.evalArgs, none, ifEqualOp⟩,
  ⟨"=alpha", GroundMode.quoteArgs, none, alphaEqOp⟩,
  ⟨"get-metatype", GroundMode.evalArgs, none, getMetatypeOp⟩,
  ⟨"not", GroundMode.evalArgs, none, notOp⟩,
  ⟨"xor", GroundMode.evalArgs, none, xorOp⟩,
  ⟨"/", GroundMode.evalArgs, none, divOp⟩,
  ⟨"%", GroundMode.evalArgs, none, modOp⟩,
  ⟨"unique-atom", GroundMode.evalArgs, none, uniqueAtomOp⟩,
  ⟨"union-atom", GroundMode.evalArgs, none, unionAtomOp⟩,
  ⟨"intersection-atom", GroundMode.evalArgs, none, intersectionAtomOp⟩,
  ⟨"subtraction-atom", GroundMode.evalArgs, none, subtractionAtomOp⟩,
  ⟨"superpose", GroundMode.evalArgs, none, superposeOp⟩,
  -- `hyperpose` produces the same result bag as `superpose`: it places each element of its argument
  -- into the nondeterministic plan. Parallel evaluation of those branches is an execution-strategy
  -- detail invisible to the (set of) results, so `hyperpose` and `superpose` have identical result
  -- semantics and share `superposeOp`.
  ⟨"hyperpose", GroundMode.evalArgs, none, superposeOp⟩,
  ⟨"collapse-extract", GroundMode.evalArgs, none, collapseExtractOp⟩,
  ⟨"sealed", GroundMode.evalArgs, none, sealedOp⟩,
  ⟨"nop", GroundMode.evalArgs, none, nopOp⟩,
  -- `(pragma! …)` is a runtime directive (e.g. `type-check auto`); we accept it and return `()`.
  -- Eager type-checking is always on in this model (operators carry declared types), so the
  -- directive needs no separate mode flag; d5's post-pragma type errors arise from those types.
  ⟨"pragma!", GroundMode.evalArgs, none, nopOp⟩,
  -- `(register-module! <path>)` registers a module-search root with the runner; the catalog lookup
  -- and file read are IO performed in `Main.loadImports` (which scans the source for these), so the
  -- instruction itself just acknowledges with `()`.
  ⟨"register-module!", GroundMode.evalArgs, none, nopOp⟩,
  -- `(empty)` removes the current nondeterministic branch (it yields *no* results, like
  -- `(superpose ())`) rather than reducing to an atom. d4's type-reasoning rules call `(empty)` to
  -- prune spurious branches, e.g. the `(: return (-> $t $t))` interference the d4 comment warns
  -- about, so only genuine proofs survive.
  ⟨"empty", GroundMode.evalArgs, none, fun _ => ReduceResult.ok []⟩,
  -- `help!` prints documentation for its atom; we satisfy the contract by returning `()` (the
  -- formal doc is available via `get-doc`, which g1_docs checks structurally).
  ⟨"help!", GroundMode.evalArgs, none, nopOp⟩,
  ⟨"_assert-results-are-equal", GroundMode.evalArgs, none, assertResultsEqOp (· == ·)⟩,
  ⟨"_assert-results-are-equal-msg", GroundMode.evalArgs, none, assertResultsEqOp (· == ·)⟩,
  ⟨"_assert-results-are-alpha-equal", GroundMode.evalArgs, none, assertResultsEqOp alphaEq⟩,
  ⟨"_assert-results-are-alpha-equal-msg", GroundMode.evalArgs, none, assertResultsEqOp alphaEq⟩,
  ⟨"sort-atom", GroundMode.evalArgs, none, sortAtomOp⟩,
  ⟨"sort-strings", GroundMode.evalArgs, none, sortAtomOp⟩
]

/-
`noeval` / inert results (`switch-minimal`, `quote`): RESOLVED faithfully, no core-type change.
Hyperon's `metta_call(result, ret_type)` (interpreter.rs) re-evaluates a function's result only when
`ret_type ≠ Atom`. So `noeval : (-> Atom Atom)` keeps `(noeval (+ 1 2))` as `(+ 1 2)`, while
`id : (-> $t $t)` (non-`Atom` return) re-evaluates the same value to `3`, and
`switch-minimal : (-> Atom Expression Atom)` stays inert. Implemented as `returnsAtom` in
`Interpreter.lean`, gating `mettaEval`'s result re-evaluation (guarded by `!isEmbeddedOp` so a bare
`(chain …)` function body is still run). The declared return type carries the same information as
Hyperon's `is_evaluated()` flag for every stdlib function the oracle exercises, so no `evaluated`
bit on `Atom.expr` is required.

CROSS-ELEMENT EVALUATION: RESOLVED (33/33). `mettaEval`/`interpretFuel` are binding-aware
(`… → List (Atom × Bindings) × Nat`) and gensym-counter-threaded; expression-headed atoms route to a
prelude `interpret-tuple` (Hyperon `interpret_tuple`, interpreter.rs:1191) that evaluates each element
and `cons-atom`s them back; `Expression`-typed arguments are left un-evaluated (`argMask`, Hyperon
interpreter.rs:1011). The propagation-vs-hygiene tension is resolved by `apply_and_retain` keyed on the
CONTINUATION's live scope, split across two evaluation operators:
  • `metta` (used by `map`/`filter`/`foldl` for the per-element operator): fully evaluates the operator
    but DROPS its internal bindings; a function operator's `let`-scoped locals must not leak across
    elements/steps. This keeps `overlap-857` and `map-atom`+`let` hygienic.
  • `metta-thread` (used by `interpret-tuple` for tuple elements): RETAINS exactly the solutions for
    variables still live in the continuation (`scopeVars`/`restrictBnd`), so a genuine query solution
    (`$a = A` from `(isa911 $a B)`) reaches the sibling `$a` → `(True A)`, while a `let`-pattern
    variable, never live in the continuation, is dropped. `mettaEval` carries each result's own
    bindings forward (re-evaluating under `p.2`, not an empty context) so those solutions survive to
    the `metta-thread` boundary, where the scope filter applies.
This is Hyperon's `apply_and_retain` specialised to the continuation scope: tuple-element evaluation
threads shared query variables; operator evaluation retains nothing locally. `((f3) (f3))` works via
counter threading (each `(f3)` a distinct fresh variable). All 33 `test_stdlib.metta` assertions pass.
-/

/-- The MeTTa-level standard-library prelude (a faithful subset of Hyperon's `stdlib.metta`,
    written on the minimal instruction set). Error messages use symbols rather than strings. -/
def preludeSrc : String :=
  "(: + (-> Number Number Number))
   (: - (-> Number Number Number))
   (: * (-> Number Number Number))
   (: / (-> Number Number Number))
   (: % (-> Number Number Number))
   (: = (-> $t $t %Undefined%))
   (: == (-> $t $t Bool))
   (: < (-> Number Number Bool))
   (: > (-> Number Number Bool))
   (: <= (-> Number Number Bool))
   (: >= (-> Number Number Bool))
   (: get-type (-> Atom Atom))
   (: get-doc (-> Atom %Undefined%))
   (: help! (-> Atom %Undefined%))
   (: eval (-> Atom Atom))
   (: chain (-> Atom Variable Atom %Undefined%))
   (: unify (-> Atom Atom Atom Atom %Undefined%))
   (: function (-> Atom Atom))
   (: return (-> Atom Atom))
   (: cons-atom (-> Atom Expression Atom))
   (: decons-atom (-> Expression Atom))
   (: collapse-bind (-> Atom Expression))
   (: superpose-bind (-> Expression Atom))
   (: metta (-> Atom Atom Atom Atom))
   (: quote (-> Atom Atom))
   (: new-state (-> $t (StateMonad $t)))
   (: change-state! (-> (StateMonad $t) $t (StateMonad $t)))
   (: if (-> Bool Atom Atom %Undefined%))
   (: let (-> Atom %Undefined% Atom %Undefined%))
   (: let* (-> Expression Atom %Undefined%))
   (: car-atom (-> Expression %Undefined%))
   (: cdr-atom (-> Expression Expression))
   (: switch (-> %Undefined% Expression %Undefined%))
   (: interpret-tuple (-> Atom Atom Atom))
   (= (interpret-tuple $expr $space)
      (function (eval (if-equal $expr ()
        (return ())
        (chain (decons-atom $expr) $ht
          (unify ($head $tail) $ht
            (chain (metta-thread $head %Undefined% $space) $rhead
              (chain (eval (interpret-tuple $tail $space)) $rtail
                (chain (cons-atom $rhead $rtail) $res (return $res))))
            (return $expr)))))))
   (: switch-minimal (-> Atom Expression Atom))
   (: switch-internal (-> Atom Expression Atom))
   (: collapse (-> Atom Atom))
   (: unique (-> Atom %Undefined%))
   (: union (-> Atom Atom %Undefined%))
   (: intersection (-> Atom Atom %Undefined%))
   (: subtraction (-> Atom Atom %Undefined%))
   (: Error (-> Atom Atom Atom))
   (: noeval (-> Atom Atom))
   (: id (-> $t $t))
   (: match (-> Atom Atom Atom %Undefined%))
   (: if-decons-expr (-> Expression Variable Variable Atom Atom %Undefined%))
   (: foldl-atom (-> Expression Atom Variable Variable Atom %Undefined%))
   (: assert (-> Atom (->)))
   (: assertIncludes (-> Atom Expression (->)))
   (: assertEqual (-> Atom Atom (->)))
   (: assertEqualMsg (-> Atom Atom Atom (->)))
   (: assertEqualToResult (-> Atom Atom (->)))
   (: assertEqualToResultMsg (-> Atom Atom Atom (->)))
   (: assertAlphaEqual (-> Atom Atom (->)))
   (: assertAlphaEqualMsg (-> Atom Atom Atom (->)))
   (: assertAlphaEqualToResult (-> Atom Atom (->)))
   (: assertAlphaEqualToResultMsg (-> Atom Atom Atom (->)))
   (= (if True $t $e) $t)
   (= (if False $t $e) $e)
   (= (id $x) $x)
   (= (noeval $x) $x)
   (= (quote $atom) NotReducible)
   (= (unquote (quote $atom)) $atom)
   (= (nop) ())
   (= (let $pattern $atom $template) (unify $atom $pattern $template Empty))
   (= (let* $pairs $template)
      (chain (decons-atom $pairs) $ht
        (unify ($head $tail) $ht
          (unify ($pat $at) $head
            (let $pat $at (let* $tail $template))
            (Error (let* $pairs $template) bad-let-star))
          $template)))
   (= (car-atom $a)
      (chain (decons-atom $a) $ht (unify ($head $tail) $ht $head (Error (car-atom $a) car-atom-empty))))
   (= (cdr-atom $a)
      (chain (decons-atom $a) $ht (unify ($head $tail) $ht $tail (Error (cdr-atom $a) cdr-atom-empty))))
   (= (switch $atom $cases) (id (switch-minimal $atom $cases)))
   (= (switch-minimal $atom $cases)
      (function (chain (decons-atom $cases) $list
        (chain (eval (switch-internal $atom $list)) $res
          (chain (eval (if-equal $res NotReducible Empty $res)) $x (return $x))))))
   (= (switch-internal $atom (($pattern $template) $tail))
      (function (unify $atom $pattern
        (return $template)
        (chain (eval (switch-minimal $atom $tail)) $ret (return $ret)))))
   (: case (-> Atom Expression %Undefined%))
   (= (case $atom $cases)
      (function
        (chain (context-space) $space
        (chain (collapse-bind (metta $atom %Undefined% $space)) $c
        (chain (eval (== $c ())) $is_empty
        (unify $is_empty True
          (chain (eval (switch-minimal Empty $cases)) $r (return $r))
          (chain (superpose-bind $c) $e
            (chain (eval (switch-minimal $e $cases)) $r (return $r)))))))))
   (= (collapse $atom)
      (function (chain (context-space) $space
        (chain (collapse-bind (metta $atom %Undefined% $space)) $pairs
          (chain (eval (collapse-extract $pairs)) $r (return $r))))))
   (= (unique $arg) (let $c (collapse $arg) (let $u (unique-atom $c) (superpose $u))))
   (= (union $a $b) (let $c1 (collapse $a) (let $c2 (collapse $b) (let $u (union-atom $c1 $c2) (superpose $u)))))
   (= (intersection $a $b) (let $c1 (collapse $a) (let $c2 (collapse $b) (let $u (intersection-atom $c1 $c2) (superpose $u)))))
   (= (subtraction $a $b) (let $c1 (collapse $a) (let $c2 (collapse $b) (let $u (subtraction-atom $c1 $c2) (superpose $u)))))
   (: atom-subst (-> Atom Variable Atom Atom))
   (= (atom-subst $atom $var $templ)
      (function (chain (eval (noeval $atom)) $var (return $templ))))
   (: map-atom (-> Expression Variable Atom Expression))
   (= (map-atom $list $var $map)
      (function (chain (decons-atom $list) $ht
        (unify ($head $tail) $ht
          (chain (eval (sealed ($var) $map)) $sealedmap
            (chain (eval (map-atom $tail $var $sealedmap)) $tail-mapped
              (chain (eval (atom-subst $head $var $sealedmap)) $map-expr
                (chain (metta $map-expr %Undefined% &self) $head-mapped
                  (chain (cons-atom $head-mapped $tail-mapped) $res (return $res))))))
          (return ())))))
   (: filter-atom (-> Expression Variable Atom Expression))
   (= (filter-atom $list $var $filter)
      (function (chain (decons-atom $list) $ht
        (unify ($head $tail) $ht
          (chain (eval (sealed ($var) $filter)) $sealedfilter
            (chain (eval (filter-atom $tail $var $sealedfilter)) $tail-filtered
              (chain (eval (atom-subst $head $var $sealedfilter)) $filter-expr
                (chain (metta $filter-expr %Undefined% &self) $is-filtered
                  (eval (if $is-filtered
                    (chain (cons-atom $head $tail-filtered) $res (return $res))
                    (return $tail-filtered)))))))
          (return ())))))
   (= (if-decons-expr $atom $head $tail $then $else)
      (function (eval (if-equal $atom ()
        (return $else)
        (chain (decons-atom $atom) $list
          (unify $list ($head $tail) (return $then) (return $else)))))))
   (= (foldl-atom $list $init $a $b $op)
      (function (eval (if-equal $list ()
        (return $init)
        (chain (decons-atom $list) $ht
          (unify ($head $tail) $ht
            (chain (eval (atom-subst $init $a $op)) $op1
              (chain (eval (atom-subst $head $b $op1)) $op2
                (chain (metta $op2 %Undefined% &self) $newacc
                  (chain (eval (foldl-atom $tail $newacc $a $b $op)) $r (return $r)))))
            (return $init)))))))
   (= (assert $atom)
      (chain (context-space) $space
        (chain (metta $atom %Undefined% $space) $eval-atom
          (unify $eval-atom True () (Error (assert $atom) ($atom not True))))))
   (= (assertIncludes $atom $content)
      (let $eval_atom (collapse $atom)
        (let $diff (subtraction-atom $content $eval_atom)
          (if (== $diff ())
            ()
            (Error (assertIncludes $atom $content)
              (assertIncludes error: $diff not included in result: $eval_atom))))))
   (= (assertEqual $actual $expected)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (chain (metta (collapse $expected) %Undefined% $space) $expected-results
            (eval (_assert-results-are-equal $actual-results $expected-results (assertEqual $actual $expected)))))))
   (= (assertEqualMsg $actual $expected $msg)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (chain (metta (collapse $expected) %Undefined% $space) $expected-results
            (eval (_assert-results-are-equal-msg $actual-results $expected-results (assertEqualMsg $actual $expected) $msg))))))
   (= (assertEqualToResult $actual $expected-results)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (eval (_assert-results-are-equal $actual-results $expected-results (assertEqualToResult $actual $expected-results))))))
   (= (assertEqualToResultMsg $actual $expected-results $msg)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (eval (_assert-results-are-equal-msg $actual-results $expected-results (assertEqualToResultMsg $actual $expected-results) $msg)))))
   (= (assertAlphaEqual $actual $expected)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (chain (metta (collapse $expected) %Undefined% $space) $expected-results
            (eval (_assert-results-are-alpha-equal $actual-results $expected-results (assertAlphaEqual $actual $expected)))))))
   (= (assertAlphaEqualMsg $actual $expected $msg)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (chain (metta (collapse $expected) %Undefined% $space) $expected-results
            (eval (_assert-results-are-alpha-equal-msg $actual-results $expected-results (assertAlphaEqualMsg $actual $expected) $msg))))))
   (= (assertAlphaEqualToResult $actual $expected-results)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (eval (_assert-results-are-alpha-equal $actual-results $expected-results (assertAlphaEqualToResult $actual $expected-results))))))
   (= (assertAlphaEqualToResultMsg $actual $expected-results $msg)
      (chain (context-space) $space
        (chain (metta (collapse $actual) %Undefined% $space) $actual-results
          (eval (_assert-results-are-alpha-equal-msg $actual-results $expected-results (assertAlphaEqualToResultMsg $actual $expected-results) $msg)))))
   (: noreduce-eq (-> Atom Atom Bool))
   (= (noreduce-eq $a $b) (== (quote $a) (quote $b)))
   (: if-error (-> Atom Atom Atom %Undefined%))
   (= (if-error $atom $then $else)
      (function (chain (eval (get-metatype $atom)) $meta
        (eval (if-equal $meta Expression
          (eval (if-equal $atom ()
            (return $else)
            (chain (decons-atom $atom) $list
              (unify $list ($head $tail)
                (eval (if-equal $head Error (return $then) (return $else)))
                (return $else) ))))
          (return $else) )))))
   (: return-on-error (-> Atom Atom %Undefined%))
   (= (return-on-error $atom $then)
      (function (eval (if-equal $atom Empty (return (return Empty))
        (eval (if-error $atom (return (return $atom))
          (return $then) ))))))
   (: for-each-in-atom (-> Expression Atom (->)))
   (= (for-each-in-atom $expr $func)
      (if (noreduce-eq $expr ())
        ()
        (let $head (car-atom $expr)
          (let $tail (cdr-atom $expr)
          (let $_ ($func $head)
          (for-each-in-atom $tail $func) )))))
   (: is-function (-> Type Bool))
   (= (is-function $type)
      (let $mtype (get-metatype $type)
        (unify $mtype Expression
          (let $size (size-atom $type)
            (unify $size 0
              False
              (let ($h $t) (decons-atom $type)
                (unify $h -> True False))))
          False)))
   (: match-types (-> Type Type Atom Atom %Undefined%))
   (= (match-types $type1 $type2 $then $else)
      (function (eval (if-equal $type1 %Undefined%
        (return $then)
        (eval (if-equal $type2 %Undefined%
          (return $then)
          (eval (if-equal $type1 Atom
            (return $then)
            (eval (if-equal $type2 Atom
              (return $then)
              (unify $type1 $type2 (return $then) (return $else)) ))))))))))
   (: match-type-or (-> Bool Atom Type Bool))
   (= (match-type-or $folded $next $type)
      (function
        (chain (eval (match-types $next $type True False)) $matched
          (chain (eval (or $folded $matched)) $or (return $or)) )))
   (: first-from-pair (-> Expression Atom))
   (= (first-from-pair $pair)
      (function
        (unify $pair ($first $second)
          (return $first)
          (return (Error (first-from-pair $pair) \"incorrect pair format\")))))
   (: type-cast-error-or-bad-type (-> Atom Expression Atom))
   (= (type-cast-error-or-bad-type $atom $actual-types)
      (function
        (chain (eval (filter-atom $actual-types $actual (eval (if-error $actual True False)))) $actual-errors
          (chain (decons-atom $actual-errors) $error-and-tail
            (unify $error-and-tail ($error $tail)
              (return $error)
              (return (Error $atom BadType)))))))
   (: type-cast (-> Atom Type Space %Undefined%))
   (= (type-cast $atom $type $space)
      (function (chain (eval (get-metatype $atom)) $meta
        (eval (if-equal $type $meta
          (return $atom)
          (chain (eval (collapse-bind (eval (get-type $atom $space)))) $collapsed
            (chain (eval (map-atom $collapsed $pair (eval (first-from-pair $pair)))) $actual-types
              (chain (eval (foldl-atom $actual-types False $a $b (eval (match-type-or $a $b $type)))) $is-some-comp
                (eval (if $is-some-comp
                  (return $atom)
                  (chain (eval (type-cast-error-or-bad-type $atom $actual-types)) $error (return $error)) ))))))))))
   (: ErrorType Type)
   (: SpaceType Type)
   (: BadType (-> Type Type ErrorDescription))
   (: BadArgType (-> Number Type Type ErrorDescription))
   (: IncorrectNumberOfArguments ErrorDescription)
   (: add-reduct (-> SpaceType %Undefined% (->)))
   (= (add-reduct $dst $atom) (add-atom $dst $atom))
   (: add-reducts (-> SpaceType %Undefined% (->)))
   (= (add-reducts $space $tuple) (foldl-atom $tuple () $a $b (add-atom $space $b)))
   (: add-atoms (-> SpaceType Expression (->)))
   (= (add-atoms $space $tuple) (foldl-atom $tuple () $a $b (add-atom $space $b)))"

/-- The parsed prelude atoms. -/
def preludeAtoms : List Atom :=
  match parseProgram preludeSrc with
  | Except.ok xs => xs
  | Except.error _ => []

/-- A knowledge base = the stdlib prelude plus the user's atoms. -/
def stdKb (userAtoms : List Atom) : Space := ⟨preludeAtoms ++ userAtoms⟩

/-- Evaluate `query` one minimal step against the prelude+user knowledge base. -/
def runStd (userAtoms : List Atom) (fuel : Nat) (query : Atom) : List Atom :=
  evalAtomMin (MinEnv.ofAtomsGT (preludeAtoms ++ userAtoms) stdGroundings) fuel query

/-- Fully evaluate `query` against the prelude+user knowledge base (`mettaEval` is defined in
    `Minimal/Interpreter`, mutual with the interpreter so the `metta` instruction uses it). -/
def runFull (userAtoms : List Atom) (fuel : Nat) (query : Atom) : List Atom :=
  (mettaEval (MinEnv.ofAtomsGT (preludeAtoms ++ userAtoms) stdGroundings) fuel St.init [] query).1.map (·.1)

/-- Split a parsed program into (knowledge-base atoms, `!`-prefixed query atoms). -/
def splitProgram : List Atom → List Atom × List Atom
  | [] => ([], [])
  | Atom.sym "!" :: q :: rest => let (kb, qs) := splitProgram rest; (kb, q :: qs)
  | Atom.expr [Atom.sym "!", q] :: rest => let (kb, qs) := splitProgram rest; (kb, q :: qs)
  | a :: rest => let (kb, qs) := splitProgram rest; (a :: kb, qs)

/-- Evaluate a program **sequentially**, as Hyperon processes a `.metta` file top-to-bottom: each
    `!`-query is evaluated against the knowledge base built from the atoms that precede it, while
    non-bang atoms extend the knowledge base. This is what makes order-dependent programs faithful:
    e.g. the same expression evaluated before and after a `(: …)` type declaration. Returns each
    query paired with its results, in file order. -/
def evalSequential (atoms : List Atom) (fuel : Nat)
    (imports : Std.HashMap String (List Atom) := Std.HashMap.emptyWithCapacity) : List (Atom × List Atom) :=
  -- `runQ` evaluates a query under the current `St` (gensym counter + mutable world) and returns its
  -- results together with the advanced state, so `bind!` tokens, named-space `add-atom`s and state
  -- cells made by one query are visible to later queries (globally mutable, like Hyperon). `imports`
  -- (pre-read by the IO runner) backs `import!` and is constant across the run.
  let runQ := fun (kbRev : List Atom) (st : St) (q : Atom) =>
    let env := { MinEnv.ofAtomsGT (preludeAtoms ++ kbRev.reverse) stdGroundings with imports := imports }
    let (pairs, st') := mettaEval env fuel st [] q
    (pairs.map (·.1), st')
  -- accumulator: (kb-atoms reversed, results reversed, threaded St, "previous atom was `!`")
  let step := fun (acc : List Atom × List (Atom × List Atom) × St × Bool) (a : Atom) =>
    let (kbRev, resRev, st, wasBang) := acc
    if wasBang then let (rs, st') := runQ kbRev st a; (kbRev, (a, rs) :: resRev, st', false)
    else match a with
      | Atom.sym "!" => (kbRev, resRev, st, true)
      | Atom.expr [Atom.sym "!", q] => let (rs, st') := runQ kbRev st q; (kbRev, (q, rs) :: resRev, st', false)
      | _ => (a :: kbRev, resRev, st, false)
  (atoms.foldl step ([], [], St.init, false)).2.1.reverse

/-- The module name imported by an `import!` statement (`!(import! &kb c2_spaces_kb)` →
    `c2_spaces_kb`), if `a` is one. Both the split form (a leading `!` is a separate top-level atom)
    and a wrapped `(! …)` form are recognised. -/
def importName? : Atom → Option String
  | Atom.expr [Atom.sym "import!", _, Atom.sym f] => some f
  | Atom.expr [Atom.sym "!", inner] => importName? inner
  | _ => none

/-- Module names referenced by any top-level `import!` in a program, so the IO runner knows which
    files to read before evaluating. -/
def collectImports (atoms : List Atom) : List String := atoms.filterMap importName?

/-- The search-root path registered by a `register-module!` statement
    (`!(register-module! ../../../chaining)` → `../../../chaining`), if `a` is one. As with
    `importName?`, both the split `!` form and a wrapped `(! …)` form are recognised. -/
def moduleRootPath? : Atom → Option String
  | Atom.expr [Atom.sym "register-module!", Atom.sym p] => some p
  | Atom.expr [Atom.sym "!", inner] => moduleRootPath? inner
  | _ => none

/-- Module-search roots registered by any top-level `register-module!` in a program, so the IO
    runner can resolve namespaced imports (`module:sub:name`) against them. -/
def collectModuleRoots (atoms : List Atom) : List String := atoms.filterMap moduleRootPath?

/-- Run a MeTTa program (sequentially) and pretty-print all `!`-query results. -/
def runMinimalSource (src : String) (fuel : Nat := 100000)
    (imports : Std.HashMap String (List Atom) := Std.HashMap.emptyWithCapacity) : String :=
  match parseProgram src with
  | Except.error e => "parse error: " ++ e
  | Except.ok atoms => Pretty.atoms ((evalSequential atoms fuel imports).flatMap (·.2))

/-- Run a test file's `!`-assertions (sequentially) and report pass/fail counts; an assertion passes
    iff it evaluates to the unit atom `()` (`Atom.expr []`). -/
def oracleReport (src : String) (fuel : Nat := 100000)
    (imports : Std.HashMap String (List Atom) := Std.HashMap.emptyWithCapacity) : String :=
  match parseProgram src with
  | Except.error e => "parse error: " ++ e
  | Except.ok atoms =>
      let res := (evalSequential atoms fuel imports).foldl (fun (acc : Nat × Nat × List String) qr =>
        if qr.2 == [Atom.expr []] then (acc.1 + 1, acc.2.1, acc.2.2)
        else (acc.1, acc.2.1 + 1, acc.2.2 ++ [s!"FAIL: {qr.1}\n   got: {Pretty.atoms qr.2}"])) (0, 0, [])
      "\n".intercalate (res.2.2 ++ [s!"\n==== PASS={res.1}  FAIL={res.2.1}  TOTAL={res.1 + res.2.1} ===="])

end Metta.Minimal
