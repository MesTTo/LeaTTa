/-
Reduction examples, checked by computation: SKI combinator steps and an RComm step that exercises
the built-in `Subst`. These confirm the matching, substitution, and rewrite-application core.

Results are compared with `BEq` (`==`) since `AST` carries `BEq`, not `DecidableEq`.
-/
import MeTTaIL.Semantics.Reduce

namespace MeTTaILTests.Reduce
open MeTTaIL

private def s0 (n : String) : AST := .sexp (.id n) []
private def vv (n : String) : AST := .var (.base n)
private def app (a b : AST) : AST := .sexp (.id "App") [a, b]
private def k1 (a : AST) : AST := .sexp (.id "K1") [a]

-- SKI ι1: `App(I, x) ~> x`. So `App(I, C)` reduces to `C`.
private def iota1 : RewriteDecl := { name := "iota1", rw := .base (app (s0 "I") (vv "x")) (vv "x") }
example : (applyBaseRewrite iota1 (app (s0 "I") (s0 "C")) == some (s0 "C")) = true := by decide

-- SKI κ2: `App(K1(x), y) ~> x`. So `App(K1(a), b)` reduces to `a`.
private def kappa2 : RewriteDecl :=
  { name := "kappa2", rw := .base (app (k1 (vv "x")) (vv "y")) (vv "x") }
example : (applyBaseRewrite kappa2 (app (k1 (s0 "a")) (s0 "b")) == some (s0 "a")) = true := by decide

-- A rewrite whose left-hand side does not match yields no reduct.
example : (applyBaseRewrite iota1 (app (s0 "K") (s0 "C")) == none) = true := by decide

-- The RHO COMM rule with `Subst`. Term `(PPar (PRecv w C (PDrop w)) (PSend C D))`: the receive on
-- channel C meets the send on C, and the received name (here `@D`) is substituted for the bound
-- name `w` in the continuation `(PDrop w)`, giving `(PDrop (NQuote D))`.
private def ppar (a b : AST) : AST := .sexp (.id "PPar") [a, b]
private def precv (y x p : AST) : AST := .sexp (.id "PRecv") [y, x, p]
private def psend (x q : AST) : AST := .sexp (.id "PSend") [x, q]
private def pdrop (n : AST) : AST := .sexp (.id "PDrop") [n]
private def nquote (p : AST) : AST := .sexp (.id "NQuote") [p]

private def rcomm : RewriteDecl :=
  { name := "RComm"
    rw := .base (ppar (precv (vv "y") (vv "x") (vv "P")) (psend (vv "x") (vv "Q")))
                (.subst (vv "P") (nquote (vv "Q")) (.base "y")) }
private def commTerm : AST := ppar (precv (vv "w") (s0 "C") (pdrop (vv "w"))) (psend (s0 "C") (s0 "D"))

example : (applyBaseRewrite rcomm commTerm == some (pdrop (nquote (s0 "D")))) = true := by decide

-- The COMM rule does not fire when the send and receive are on different channels.
private def commTermMismatch : AST :=
  ppar (precv (vv "w") (s0 "C") (pdrop (vv "w"))) (psend (s0 "E") (s0 "D"))
example : (applyBaseRewrite rcomm commTermMismatch == none) = true := by decide

end MeTTaILTests.Reduce
