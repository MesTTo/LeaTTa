import MettaHyperonFull.Core.Grounding

namespace Metta

namespace Builtins

/-- Extract a Lean `Int` from an `Int`-grounded atom (`none` for anything else). -/
def toInt? : Atom → Option Int
  | Atom.gnd (Ground.int n) => some n
  | _ => none

/-- Extract a Lean `Bool` from a `Bool`-grounded atom or the `True`/`False` symbols. -/
def toBool? : Atom → Option Bool
  | Atom.gnd (Ground.bool b) => some b
  | Atom.sym "True" => some true
  | Atom.sym "False" => some false
  | _ => none

/-- Lift a binary `Int` operation to a grounded op on exactly two `Int` atoms (else an arg error). -/
def intBin (f : Int → Int → Int) : List Atom → ReduceResult
  | [a,b] => match toInt? a, toInt? b with
      | some x, some y => ReduceResult.ok [Atom.gnd (Ground.int (f x y))]
      | _, _ => ReduceResult.incorrectArgument "expected two Int atoms"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Lift a binary `Int` predicate to a grounded op returning a `Bool` atom (on two `Int` atoms). -/
def intCmp (f : Int → Int → Bool) : List Atom → ReduceResult
  | [a,b] => match toInt? a, toInt? b with
      | some x, some y => ReduceResult.ok [Atom.gnd (Ground.bool (f x y))]
      | _, _ => ReduceResult.incorrectArgument "expected two Int atoms"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Polymorphic arithmetic on `Int`/`Float` atoms. Matching Hyperon's runtime, a mixed `Int`/`Float`
    pair promotes the `Int` operand to `Float`. Non-numeric arguments return `incorrectArgument`,
    which the evaluator surfaces as `NotReducible`; the `BadArgType` error is separate, coming from
    the type layer's declared-signature check. -/
def numBin (fi : Int → Int → Int) (ff : Float → Float → Float) : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] => ReduceResult.ok [Atom.gnd (Ground.int (fi a b))]
  | [Atom.gnd (Ground.float a), Atom.gnd (Ground.float b)] => ReduceResult.ok [Atom.gnd (Ground.float (ff a b))]
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.float b)] => ReduceResult.ok [Atom.gnd (Ground.float (ff (Float.ofInt a) b))]
  | [Atom.gnd (Ground.float a), Atom.gnd (Ground.int b)] => ReduceResult.ok [Atom.gnd (Ground.float (ff a (Float.ofInt b)))]
  | [_, _] => ReduceResult.incorrectArgument "expected two Int or two Float atoms"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Polymorphic comparison on `Int`/`Float` atoms (mixed pairs promote the `Int`), returning Bool. -/
def numCmp (fi : Int → Int → Bool) (ff : Float → Float → Bool) : List Atom → ReduceResult
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.int b)] => ReduceResult.ok [Atom.gnd (Ground.bool (fi a b))]
  | [Atom.gnd (Ground.float a), Atom.gnd (Ground.float b)] => ReduceResult.ok [Atom.gnd (Ground.bool (ff a b))]
  | [Atom.gnd (Ground.int a), Atom.gnd (Ground.float b)] => ReduceResult.ok [Atom.gnd (Ground.bool (ff (Float.ofInt a) b))]
  | [Atom.gnd (Ground.float a), Atom.gnd (Ground.int b)] => ReduceResult.ok [Atom.gnd (Ground.bool (ff a (Float.ofInt b)))]
  | [_, _] => ReduceResult.incorrectArgument "expected two Int or two Float atoms"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Lift a binary `Bool` operation to a grounded op on exactly two `Bool` atoms (else an arg error). -/
def boolBin (f : Bool → Bool → Bool) : List Atom → ReduceResult
  | [a,b] => match toBool? a, toBool? b with
      | some x, some y => ReduceResult.ok [Atom.gnd (Ground.bool (f x y))]
      | _, _ => ReduceResult.incorrectArgument "expected two Bool atoms"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Grounded `==`: structural equality of two atoms, returning a `Bool` atom, but **propagating
    errors**: an argument that reduced to an `(Error …)` becomes the result rather than being
    compared (Hyperon's behaviour for `==`; kept local to `==` so `assert*` can still compare errors). -/
def eqAtom : List Atom → ReduceResult
  | [a,b] =>
      -- Error propagation: `==` lifts an argument that reduced to an `(Error …)` to be its own
      -- result, instead of comparing against the error atom. Error promotion is Hyperon's behaviour, e.g.
      -- `(== 4 (+ ln 2))` with `(: ln LN)` declared yields `(Error (+ ln 2) (BadArgType 1 Number LN))`
      -- (the type error raised by `(+ ln 2)`), not `False`. Ops like `assert*` instead need to
      -- *compare* error results, so this lift is local to `==` rather than in the generic
      -- grounded-call path (a blanket lift regresses the `assert*`/`test_stdlib` suites).
      if a.isError then ReduceResult.ok [a]
      else if b.isError then ReduceResult.ok [b]
      else ReduceResult.ok [Atom.gnd (Ground.bool (a == b))]
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Grounded `cons-atom`: prepend a head atom to a tuple, so `(cons-atom h (a b)) = (h a b)`. -/
def consAtom : List Atom → ReduceResult
  | [h, Atom.expr t] => ReduceResult.ok [Atom.expr (h :: t)]
  | [h, t] => ReduceResult.ok [Atom.expr [h,t]]
  | _ => ReduceResult.incorrectArgument "expected head and tail"

/-- Grounded `decons-atom`: split a non-empty tuple into `(head (tail …))` (empty → `Empty`). -/
def deconsAtom : List Atom → ReduceResult
  | [Atom.expr (h :: t)] => ReduceResult.ok [Atom.expr [h, Atom.expr t]]
  | [Atom.expr []] => ReduceResult.ok [Atom.empty]
  | _ => ReduceResult.incorrectArgument "expected non-empty expression"

/-- Grounded `car-atom`: the head of a non-empty tuple. -/
def carAtom : List Atom → ReduceResult
  | [Atom.expr (h :: _)] => ReduceResult.ok [h]
  | _ => ReduceResult.incorrectArgument "expected non-empty expression"

/-- Grounded `cdr-atom`: the tail of a non-empty tuple. -/
def cdrAtom : List Atom → ReduceResult
  | [Atom.expr (_ :: t)] => ReduceResult.ok [Atom.expr t]
  | _ => ReduceResult.incorrectArgument "expected non-empty expression"

/-- Grounded `size-atom`: the number of children of a tuple (or `Atom.size` for a non-expression). -/
def sizeAtom : List Atom → ReduceResult
  | [Atom.expr xs] => ReduceResult.ok [Atom.gnd (Ground.int (Int.ofNat xs.length))]
  | [a] => ReduceResult.ok [Atom.gnd (Ground.int (Int.ofNat (Atom.size a)))]
  | _ => ReduceResult.incorrectArgument "expected one atom"

/-- Coerce a numeric atom to `Float` (an `Int` is promoted), else `none`. -/
def toFloat? : Atom → Option Float
  | Atom.gnd (Ground.float x) => some x
  | Atom.gnd (Ground.int n) => some (Float.ofInt n)
  | _ => none

/-- Unary `f64` math op (`sqrt`/`sin`/`cos`/`tan`/`asin`/`acos`/`atan`-math): coerce the argument to
    `Float`, apply `ff`, return a `Float` (Hyperon `runner/stdlib/math.rs`). -/
def floatUn (ff : Float → Float) : List Atom → ReduceResult
  | [a] => match toFloat? a with
      | some x => ReduceResult.ok [Atom.gnd (Ground.float (ff x))]
      | none => ReduceResult.incorrectArgument "expected a Number"
  | _ => ReduceResult.incorrectArgument "expected exactly one argument"

/-- Binary `f64` math op (`pow-math base exp`, `log-math base input`): both arguments coerced to
    `Float`, result a `Float`. -/
def floatBin (ff : Float → Float → Float) : List Atom → ReduceResult
  | [a, b] => match toFloat? a, toFloat? b with
      | some x, some y => ReduceResult.ok [Atom.gnd (Ground.float (ff x y))]
      | _, _ => ReduceResult.incorrectArgument "expected two Numbers"
  | _ => ReduceResult.incorrectArgument "expected exactly two arguments"

/-- Rounding math op (`abs`/`trunc`/`ceil`/`floor`/`round`-math): an `Int` is integral already, so it
    is returned with `fi` applied (identity except `abs`); a `Float` has `ff` applied, staying `Float`.
    Hyperon matches `Number::Integer`/`Number::Float` the same way. -/
def numRound (fi : Int → Int) (ff : Float → Float) : List Atom → ReduceResult
  | [Atom.gnd (Ground.int n)] => ReduceResult.ok [Atom.gnd (Ground.int (fi n))]
  | [Atom.gnd (Ground.float x)] => ReduceResult.ok [Atom.gnd (Ground.float (ff x))]
  | [_] => ReduceResult.incorrectArgument "expected a Number"
  | _ => ReduceResult.incorrectArgument "expected exactly one argument"

/-- Float predicate (`isnan-math`/`isinf-math`): an `Int` is never NaN/∞ (→ `False`); a `Float`
    uses `fb`. -/
def floatPred (fb : Float → Bool) : List Atom → ReduceResult
  | [Atom.gnd (Ground.int _)] => ReduceResult.ok [Atom.gnd (Ground.bool false)]
  | [Atom.gnd (Ground.float x)] => ReduceResult.ok [Atom.gnd (Ground.bool (fb x))]
  | [_] => ReduceResult.incorrectArgument "expected a Number"
  | _ => ReduceResult.incorrectArgument "expected exactly one argument"

/-- Truncate a `Float` toward zero (Lean's `Float` has no `trunc`; toward-zero = floor for `x ≥ 0`,
    ceil otherwise). -/
def ftrunc (x : Float) : Float := if x ≥ 0.0 then x.floor else x.ceil

/-- The `*-math` grounded ops from Hyperon's `runner/stdlib/math.rs`: the f64 transcendental and
    rounding operations (`abs`, `sqrt`, `pow`, `log`, the trig family, the rounding family, and the
    `isnan`/`isinf` predicates). -/
def mathTable : GroundingTable := [
  ⟨"sqrt-math", GroundMode.evalArgs, none, floatUn Float.sqrt⟩,
  ⟨"sin-math", GroundMode.evalArgs, none, floatUn Float.sin⟩,
  ⟨"cos-math", GroundMode.evalArgs, none, floatUn Float.cos⟩,
  ⟨"tan-math", GroundMode.evalArgs, none, floatUn Float.tan⟩,
  ⟨"asin-math", GroundMode.evalArgs, none, floatUn Float.asin⟩,
  ⟨"acos-math", GroundMode.evalArgs, none, floatUn Float.acos⟩,
  ⟨"atan-math", GroundMode.evalArgs, none, floatUn Float.atan⟩,
  ⟨"pow-math", GroundMode.evalArgs, none, floatBin Float.pow⟩,
  ⟨"log-math", GroundMode.evalArgs, none, floatBin (fun base input => Float.log input / Float.log base)⟩,
  ⟨"abs-math", GroundMode.evalArgs, none, numRound (fun n => Int.ofNat n.natAbs) Float.abs⟩,
  ⟨"trunc-math", GroundMode.evalArgs, none, numRound id ftrunc⟩,
  ⟨"ceil-math", GroundMode.evalArgs, none, numRound id Float.ceil⟩,
  ⟨"floor-math", GroundMode.evalArgs, none, numRound id Float.floor⟩,
  ⟨"round-math", GroundMode.evalArgs, none, numRound id Float.round⟩,
  ⟨"isnan-math", GroundMode.evalArgs, none, floatPred Float.isNaN⟩,
  ⟨"isinf-math", GroundMode.evalArgs, none, floatPred Float.isInf⟩
]

/-- `min-atom`/`max-atom` (Hyperon `atom.rs`): the minimum/maximum of an expression of numbers,
    compared as `f64` and returned as a `Float`. A non-expression argument returns `incorrectArgument`
    (surfaced as `NotReducible`); an empty expression or a non-number child raises a runtime error. -/
def minMaxAtom (isMin : Bool) (name : String) : List Atom → ReduceResult
  | [Atom.expr xs] =>
      match xs.mapM toFloat? with
      | none => ReduceResult.runtimeError "Only numbers are allowed in expression"
      | some [] => ReduceResult.runtimeError "Empty expression"
      | some (y :: ys) =>
          ReduceResult.ok [Atom.gnd (Ground.float
            (ys.foldl (fun acc z => if isMin then (if z < acc then z else acc)
                                    else (if z > acc then z else acc)) y))]
  | _ => ReduceResult.incorrectArgument (name ++ " expects one argument: expression")

/-- `index-atom` (Hyperon `atom.rs`): the 0-based element of an expression at a given index, or an
    out-of-bounds error. -/
def indexAtom : List Atom → ReduceResult
  | [Atom.expr xs, n] =>
      match toInt? n with
      | some i =>
          if i < 0 then ReduceResult.runtimeError "Index is out of bounds"
          else match xs[i.toNat]? with
            | some a => ReduceResult.ok [a]
            | none => ReduceResult.runtimeError "Index is out of bounds"
      | none => ReduceResult.incorrectArgument "index-atom expects two arguments: expression and atom"
  | _ => ReduceResult.incorrectArgument "index-atom expects two arguments: expression and atom"

/-- The arithmetic / boolean / list-surgery grounding core every knowledge base starts with:
    `+ - * < <= > >= == and or`, the list ops `cons-atom`/`decons-atom`/`car-atom`/`cdr-atom`/`size-atom`,
    the `min-atom`/`max-atom`/`index-atom` number-and-list utilities, and the `*-math` f64 operations
    (`mathTable`). The stdlib's `stdGroundings` extends this table. -/
def table : GroundingTable := mathTable ++ [
  ⟨"+", GroundMode.evalArgs, none, numBin (· + ·) (· + ·)⟩,
  ⟨"-", GroundMode.evalArgs, none, numBin (· - ·) (· - ·)⟩,
  ⟨"*", GroundMode.evalArgs, none, numBin (· * ·) (· * ·)⟩,
  ⟨"<", GroundMode.evalArgs, none, numCmp (· < ·) (· < ·)⟩,
  ⟨"<=", GroundMode.evalArgs, none, numCmp (· ≤ ·) (· ≤ ·)⟩,
  ⟨">", GroundMode.evalArgs, none, numCmp (fun a b => b < a) (fun a b => b < a)⟩,
  ⟨">=", GroundMode.evalArgs, none, numCmp (fun a b => b ≤ a) (fun a b => b ≤ a)⟩,
  ⟨"==", GroundMode.evalArgs, none, eqAtom⟩,
  ⟨"and", GroundMode.evalArgs, none, boolBin (fun x y => x && y)⟩,
  ⟨"or", GroundMode.evalArgs, none, boolBin (fun x y => x || y)⟩,
  ⟨"cons-atom", GroundMode.evalArgs, none, consAtom⟩,
  ⟨"decons-atom", GroundMode.evalArgs, none, deconsAtom⟩,
  ⟨"car-atom", GroundMode.evalArgs, none, carAtom⟩,
  ⟨"cdr-atom", GroundMode.evalArgs, none, cdrAtom⟩,
  ⟨"size-atom", GroundMode.evalArgs, none, sizeAtom⟩,
  ⟨"min-atom", GroundMode.evalArgs, none, minMaxAtom true "min-atom"⟩,
  ⟨"max-atom", GroundMode.evalArgs, none, minMaxAtom false "max-atom"⟩,
  ⟨"index-atom", GroundMode.evalArgs, none, indexAtom⟩
]

end Builtins

end Metta
