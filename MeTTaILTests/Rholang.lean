/-
Module: MeTTaILTests.Rholang
Layer: Tests
Purpose: The Rholang oracle, a machine-checked cross-test against the real MeTTaIL tool.
  `UnivAlg.module` and `Rholang.module` are encoded here as Lean `Module` values, transcribed from
  the parsed AST the Scala tool prints. The checks assert that our elaborator, desugar, type-lift,
  and monomorphize passes produce exactly the presentations the tool prints (the Interpreted,
  Desugared, Hypercubed, and Generated-BNFC stages of `FreeRholang()`): the sorts Proc and Name,
  eight constructors, ten equations, and four rewrites. So our pipeline agrees with MeTTaIL on the
  flagship example. The category checker is also checked to reject ill-formed input.
Imports: MeTTaIL.Theory.Elaborate, MeTTaIL.Transform.Desugar, MeTTaIL.Transform.TypeLift,
  MeTTaIL.Transform.Monomorphize
Trusted boundary: none
Main exports: example oracle checks against expectedRholang, expectedDesugared, expectedGenerated,
  and the type-lifted terms; no reusable definitions (the transcription helpers are private).
Open obligations: none
-/
import MeTTaIL.Theory.Elaborate
import MeTTaIL.Transform.Desugar
import MeTTaIL.Transform.TypeLift
import MeTTaIL.Transform.Monomorphize

namespace MeTTaILTests.Rholang
open MeTTaIL

-- The oracle is discharged by `decide`, which the kernel checks using only the standard axioms. We
-- deliberately do not use `native_decide` (it bypasses the kernel and is outside the trusted base).
-- Elaborating the whole Rholang theory chain and comparing it to the expected presentation is a
-- large closed computation, so the elaboration heartbeat limit is raised. The proof stays
-- kernel-checked; only the elaborator's allocation budget changes.
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Encoding helpers (compact constructors for the transcription) -/

private def idc (s : String) : Cat := .idCat s
private def v (s : String) : AST := .var (.base s)
private def sx (l : String) (args : List AST) : AST := .sexp (.id l) args
private def tm (s : String) : Item := .terminal s
private def nt (c : String) : Item := .nterminal (.idCat c)
private def rule (l c : String) (items : List Item) : Rule := { label := .id l, cat := .idCat c, items }
private def eq (l r : AST) : Equation := .impl l r
private def rdecl (n : String) (rw : Rewrite) : RewriteDecl := { name := n, rw }
private def hyp (s t : String) : Hyp := { src := .base s, tgt := .base t }
private def param (i t : String) : VarDecl := { ident := i, theoryType := .base t }

/-! ### Function symbols, in their various stages -/

private def rOne : Rule := rule "One" "Elem" [tm "1"]
private def rMult : Rule := rule "Mult" "Elem" [tm "(", nt "Elem", tm "*", nt "Elem", tm ")"]
private def rZero : Rule := rule "Zero" "Elem" [tm "0"]
private def rPlus : Rule := rule "Plus" "Elem" [tm "(", nt "Elem", tm "+", nt "Elem", tm ")"]

private def rPZero : Rule := rule "PZero" "Proc" [tm "0"]
private def rPPar : Rule := rule "PPar" "Proc" [tm "(", nt "Proc", tm "|", nt "Proc", tm ")"]
private def rPRepl : Rule := rule "PRepl" "Proc" [tm "!", nt "Proc"]
private def rPNew : Rule :=
  { label := .id "PNew", cat := idc "Proc"
    items := [tm "new", .bindNTerminal "x" (idc "Name"), tm "in", .absNTerminal "x" (.nterminal (idc "Proc"))] }
private def rPDrop : Rule := rule "PDrop" "Proc" [tm "*", nt "Name"]
private def rNQuote : Rule := rule "NQuote" "Name" [tm "@", nt "Proc"]
private def rPSend : Rule := rule "PSend" "Proc" [nt "Name", tm "!", tm "(", nt "Proc", tm ")"]
private def rPRecv : Rule :=
  { label := .id "PRecv", cat := idc "Proc"
    items := [tm "for", tm "(", .bindNTerminal "x" (idc "Name"), tm "<-", nt "Name", tm ")", tm "{",
              .absNTerminal "x" (.nterminal (idc "Proc")), tm "}"] }

/-! ### The final equations and rewrites (with the post-rename labels) -/

private def eAssoc : Equation := eq (sx "PPar" [sx "PPar" [v "x", v "y"], v "z"]) (sx "PPar" [v "x", sx "PPar" [v "y", v "z"]])
private def eRUnit : Equation := eq (sx "PPar" [v "x", sx "PZero" []]) (v "x")
private def eLUnit : Equation := eq (sx "PPar" [sx "PZero" [], v "x"]) (v "x")
private def eComm : Equation := eq (sx "PPar" [v "x", v "y"]) (sx "PPar" [v "y", v "x"])
private def eFresh : Equation :=
  .fresh "x" "Q" (eq (sx "PPar" [sx "PNew" [v "x", v "P"], v "Q"]) (sx "PNew" [v "x", sx "PPar" [v "P", v "Q"]]))
private def eNewIdem : Equation := eq (sx "PNew" [v "x", sx "PNew" [v "x", v "P"]]) (sx "PNew" [v "x", v "P"])
private def eNewSwap : Equation := eq (sx "PNew" [v "x", sx "PNew" [v "y", v "P"]]) (sx "PNew" [v "y", sx "PNew" [v "x", v "P"]])
private def eRepl : Equation := eq (sx "PRepl" [v "P"]) (sx "PPar" [v "P", sx "PRepl" [v "P"]])
private def eQD1 : Equation := eq (sx "NQuote" [sx "PDrop" [v "N"]]) (v "N")
private def eQD2 : Equation := eq (sx "PDrop" [sx "NQuote" [v "P"]]) (v "P")

private def wRPar1 : RewriteDecl :=
  rdecl "RPar1" (.ctx (hyp "Src" "Tgt") (.base (sx "PPar" [v "Src", v "Q"]) (sx "PPar" [v "Tgt", v "Q"])))
private def wRPar2 : RewriteDecl :=
  rdecl "RPar2" (.ctx (hyp "Src1" "Tgt1") (.ctx (hyp "Src2" "Tgt2")
    (.base (sx "PPar" [v "Src1", v "Src2"]) (sx "PPar" [v "Tgt1", v "Tgt2"]))))
private def wRNew : RewriteDecl :=
  rdecl "RNew" (.ctx (hyp "Src" "Tgt") (.base (sx "PNew" [v "x", v "Src"]) (sx "PNew" [v "x", v "Tgt"])))
private def wRComm : RewriteDecl :=
  rdecl "RComm" (.base (sx "PPar" [sx "PRecv" [v "y", v "x", v "P"], sx "PSend" [v "x", v "Q"]])
    (.subst (v "P") (sx "NQuote" [v "Q"]) (.base "y")))

/-! ### The ground-truth presentation (the tool's `[Interpreted Presentation]`) -/

private def expectedRholang : Presentation :=
  .mk [idc "Proc", idc "Name"]
      [rPZero, rPPar, rPRepl, rPNew, rPDrop, rNQuote, rPSend, rPRecv]
      [eAssoc, eRUnit, eLUnit, eComm, eFresh, eNewIdem, eNewSwap, eRepl, eQD1, eQD2]
      [wRPar1, wRPar2, wRNew, wRComm]
      []

/-! ### The theory declarations, transcribed from the module ASTs -/

private def emptySetBody : TheoryInst := .addExports .empty [.base (idc "Elem")]

private def monoidBody : TheoryInst :=
  .addEquations (.addTerms (.ref "s") [rOne, rMult])
    [ eq (sx "Mult" [sx "Mult" [v "x", v "y"], v "z"]) (sx "Mult" [v "x", sx "Mult" [v "y", v "z"]]),
      eq (sx "Mult" [v "x", sx "One" []]) (v "x"),
      eq (sx "Mult" [sx "One" [], v "x"]) (v "x") ]

private def commMonoidBody : TheoryInst :=
  .addEquations
    (.addReplacements (.ref "m")
      [ { perm := [], target := .id "One", cat := idc "Elem", newDef := rZero },
        { perm := [0, 1], target := .id "Mult", cat := idc "Elem", newDef := rPlus } ])
    [ eq (sx "Plus" [v "x", v "y"]) (sx "Plus" [v "y", v "x"]) ]

private def parMonoidBody : TheoryInst :=
  .addRewrites
    (.addReplacements
      (.addExports (.ref "cm") [.rename (idc "Elem") (idc "Proc")])
      [ { perm := [], target := .id "Zero", cat := idc "Proc", newDef := rPZero },
        { perm := [0, 1], target := .id "Plus", cat := idc "Proc", newDef := rPPar } ])
    [ wRPar1, wRPar2 ]

private def newReplCalcBody : TheoryInst :=
  .addRewrites
    (.addEquations (.addTerms (.addExports (.ref "pm") [.base (idc "Name")]) [rPRepl, rPNew])
      [ eFresh, eNewIdem, eNewSwap, eRepl ])
    [ wRNew ]

private def quoteDropCalcBody : TheoryInst :=
  .addEquations (.addTerms (.addExports (.ref "pm") [.base (idc "Name")]) [rPDrop, rNQuote])
    [ eQD1, eQD2 ]

private def rhoCalcBody : TheoryInst :=
  .addRewrites (.addTerms (.ref "qd") [rPSend, rPRecv]) [ wRComm ]

private def rholangBody : TheoryInst := .disj (.ref "nr") (.ref "r")

private def freeRholangBody : TheoryInst :=
  .letIn "s" (.ctor (.qualified "u" (.base "EmptySet")) [])
  (.letIn "m" (.ctor (.qualified "u" (.base "Monoid")) [.ref "s"])
  (.letIn "cm" (.ctor (.qualified "u" (.base "CommutativeMonoid")) [.ref "m"])
  (.letIn "pm" (.ctor (.base "ParMonoid") [.ref "cm"])
  (.letIn "qd" (.ctor (.base "QuoteDropCalc") [.ref "pm"])
  (.letIn "nr" (.ctor (.base "NewReplCalc") [.ref "pm"])
  (.letIn "rc" (.ctor (.base "RhoCalc") [.ref "qd"])
  (.letIn "rl" (.ctor (.base "Rholang") [.ref "nr", .ref "rc"])
  (.ref "rl"))))))))

private def univAlg : Module :=
  { name := "UnivAlg"
    theories :=
      [ { name := "EmptySet", params := [], body := emptySetBody },
        { name := "Monoid", params := [param "s" "EmptySet"], body := monoidBody },
        { name := "CommutativeMonoid", params := [param "m" "Monoid"], body := commMonoidBody } ] }

private def rholangMod : Module :=
  { name := "Rholang"
    theories :=
      [ { name := "ParMonoid", params := [{ ident := "cm", theoryType := .qualified "u" (.base "CommutativeMonoid") }], body := parMonoidBody },
        { name := "NewReplCalc", params := [param "pm" "ParMonoid"], body := newReplCalcBody },
        { name := "QuoteDropCalc", params := [param "pm" "ParMonoid"], body := quoteDropCalcBody },
        { name := "RhoCalc", params := [param "qd" "QuoteDropCalc"], body := rhoCalcBody },
        { name := "Rholang", params := [param "nr" "NewReplCalc", param "r" "RhoCalc"], body := rholangBody },
        { name := "FreeRholang", params := [], body := freeRholangBody } ] }

private def oracleCtx : ElabCtx := { modules := [univAlg, rholangMod], env := [] }

/-- The entry point of the module: `theory FreeRholang()`. -/
private def entry : TheoryInst := .ctor (.base "FreeRholang") []

/-- THE ORACLE: our elaborator produces exactly the presentation the real MeTTaIL tool prints for
    `FreeRholang()`. -/
example : ((elaborate oracleCtx entry).toOption == some expectedRholang) = true := by decide

/-! ### Desugar oracle: matches the tool's `[Desugared Presentation]` -/

private def rPNewToArrow : Rule :=
  { label := .id "PNewToArrow", cat := idc "Proc"
    items := [tm "PNewToArrow", tm "(", .nterminal (.arrow (idc "Name") (idc "Proc")), tm ")"] }
private def rPRecvToArrow : Rule :=
  { label := .id "PRecvToArrow", cat := idc "Proc"
    items := [tm "PRecvToArrow", tm "(", nt "Name", .nterminal (.arrow (idc "Name") (idc "Proc")), tm ")"] }

private def expectedDesugared : Presentation :=
  .mk [idc "Proc", idc "Name"]
      [rPZero, rPPar, rPRepl, rPNew, rPNewToArrow, rPDrop, rNQuote, rPSend, rPRecv, rPRecvToArrow]
      [eAssoc, eRUnit, eLUnit, eComm, eFresh, eNewIdem, eNewSwap, eRepl, eQD1, eQD2]
      [wRPar1, wRPar2, wRNew, wRComm]
      []

/-- ORACLE: desugaring the elaborated Rholang matches the tool's `[Desugared Presentation]` (the
    `PNewToArrow` and `PRecvToArrow` companions inserted after `PNew` and `PRecv`). -/
example : (desugarBinds expectedRholang == expectedDesugared) = true := by decide

/-! ### Monomorphize oracle: matches the tool's `[Generated BNFC]` grammar -/

private def aSort : Cat := idc "ArrowCCName_ProcDD"
private def rPNewToArrowMono : Rule :=
  { label := .id "PNewToArrow", cat := idc "Proc", items := [tm "PNewToArrow", tm "(", .nterminal aSort, tm ")"] }
private def rPRecvToArrowMono : Rule :=
  { label := .id "PRecvToArrow", cat := idc "Proc", items := [tm "PRecvToArrow", tm "(", nt "Name", .nterminal aSort, tm ")"] }
private def rApp : Rule :=
  { label := .id "AppCCName_ProcDD", cat := idc "Proc", items := [tm "α", tm "{", .nterminal aSort, tm "(", nt "Name", tm ")", tm "}"] }
private def rIdentArrow : Rule := { label := .id "IdentCCName_ProcDD", cat := aSort, items := [nt "Ident"] }
private def rLam : Rule :=
  { label := .id "LamCCName_ProcDD", cat := aSort, items := [tm "λ", tm "{", tm "(", nt "Ident", tm ")", tm "=>", nt "Proc", tm "}"] }
private def rIdentDom : Rule := { label := .id "IdentCCNameDD", cat := idc "Name", items := [nt "Ident"] }

private def expectedGenerated : Presentation :=
  .mk [idc "Proc", idc "Name"]
      [rPZero, rPPar, rPRepl, rPNew, rPNewToArrowMono, rPDrop, rNQuote, rPSend, rPRecv, rPRecvToArrowMono,
       rApp, rIdentArrow, rLam, rIdentDom]
      [eAssoc, eRUnit, eLUnit, eComm, eFresh, eNewIdem, eNewSwap, eRepl, eQD1, eQD2]
      [wRPar1, wRPar2, wRNew, wRComm]
      []

/-- ORACLE: monomorphizing the desugared Rholang matches the tool's `[Generated BNFC]` grammar (the
    arrow `Name -> Proc` becomes `ArrowCCName_ProcDD`, with the `App`/`Ident`/`Lam` constructors). -/
example : (monomorphize expectedDesugared == expectedGenerated) = true := by decide

/-! ### `free` instantiation -/

private def eMAssoc : Equation :=
  eq (sx "Mult" [sx "Mult" [v "x", v "y"], v "z"]) (sx "Mult" [v "x", sx "Mult" [v "y", v "z"]])
private def eMRUnit : Equation := eq (sx "Mult" [v "x", sx "One" []]) (v "x")
private def eMLUnit : Equation := eq (sx "Mult" [sx "One" [], v "x"]) (v "x")

/-- The presentation `free(Monoid)` should produce: free-instantiate the `EmptySet` parameter (no
    parameters of its own, so just the sort `Elem`), then add the monoid symbols and laws. -/
private def expectedMonoid : Presentation :=
  .mk [idc "Elem"] [rOne, rMult] [eMAssoc, eMRUnit, eMLUnit] [] []

/-- `free` recursively instantiates a theory's parameters: `free(Monoid)` fills `Monoid`'s `EmptySet`
    parameter by free-instantiating `EmptySet`, then elaborates the body. -/
example : ((elaborate oracleCtx (.free (.base "Monoid"))).toOption == some expectedMonoid) = true := by
  decide

/-! ### The category checker rejects ill-formed input -/

/-- A rewrite whose right-hand side has a variable `Bad` bound neither on the left nor by a premise.
    The category checker rejects it, so elaboration fails. -/
private def badRewrite : RewriteDecl :=
  rdecl "RBad" (.base (sx "PPar" [v "Src", v "Q"]) (sx "PPar" [v "Bad", v "Q"]))

example : (elaborate oracleCtx (.addRewrites .empty [badRewrite])).toOption = none := rfl

/-- An equation whose two sides have incompatible categories (`Proc` vs `Name`) is rejected. -/
private def badEquation : Equation := eq (sx "PZero" []) (sx "NQuote" [v "P"])

example :
    (elaborate oracleCtx
      (.addEquations (.addTerms .empty [rPZero, rNQuote]) [badEquation])).toOption = none := rfl

/-! ### Type-lift oracle: matches the tool's `[Hypercubed Presentation]` -/

/-- `T(Name -> Proc) = Product{ Name ; (Name -> Proc) }`, the type-lift of the arrow argument. -/
private def pNameArrow : Cat := .prod [idc "Name", .arrow (idc "Name") (idc "Proc")]

private def tl (n c : String) (items : List Item) : Rule :=
  { label := .id n, cat := idc c, items := tm n :: tm "(" :: items ++ [tm ")"] }

private def cPZero : Rule := tl "TypeLiftCCPZeroDD" "Proc" []
private def cPPar : Rule := tl "TypeLiftCCPParDD" "Proc" [nt "Proc", nt "Proc"]
private def cPRepl : Rule := tl "TypeLiftCCPReplDD" "Proc" [nt "Proc"]
private def cPNewToArrow : Rule := tl "TypeLiftCCPNewToArrowDD" "Proc" [.nterminal pNameArrow]
private def cPDrop : Rule := tl "TypeLiftCCPDropDD" "Proc" [nt "Name"]
private def cNQuote : Rule := tl "TypeLiftCCNQuoteDD" "Name" [nt "Proc"]
private def cPSend : Rule := tl "TypeLiftCCPSendDD" "Proc" [nt "Name", nt "Proc", nt "Name"]
private def cPRecvToArrow : Rule :=
  tl "TypeLiftCCPRecvToArrowDD" "Proc" [nt "Name", .nterminal pNameArrow, nt "Name"]

/-- The terms of the tool's `[Hypercubed Presentation]`: the ten desugared rules plus the eight
    `TypeLiftCC..DD` companions. The companion order the tool prints is an artifact of Scala's
    HashMap iteration, so the oracle compares the term *set*, not the order. -/
private def expectedHCTerms : List Rule :=
  [rPZero, rPPar, rPRepl, rPNew, rPNewToArrow, rPDrop, rNQuote, rPSend, rPRecv, rPRecvToArrow,
   cPZero, cPPar, cPRepl, cPNewToArrow, cPDrop, cNQuote, cPSend, cPRecvToArrow]

/-- Order-insensitive list equality for distinct elements (a permutation check). -/
private def sameSet {α : Type} [BEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all (fun x => b.contains x) && b.all (fun x => a.contains x)

/-- ORACLE: type-lifting the desugared Rholang produces the same set of terms as the tool's
    `[Hypercubed Presentation]` (the eight `TypeLiftCC..DD` companions with the `T`-lifted arities,
    plus the duplicated-channel extra `Name` on `PSend` and `PRecvToArrow`). Equations and rewrites
    are carried through unchanged. -/
example : sameSet (typeLift expectedDesugared).terms expectedHCTerms = true := by decide
example : ((typeLift expectedDesugared).equations == expectedDesugared.equations) = true := by decide
example : ((typeLift expectedDesugared).rewrites == expectedDesugared.rewrites) = true := by decide

end MeTTaILTests.Rholang
