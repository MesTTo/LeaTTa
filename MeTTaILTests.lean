/-
Machine-checked sanity tests for the MeTTaIL elaborator. These are small oracle checks: elaborate a
theory instance and compare the result to a hand-written expected presentation. The full
cross-test against the Scala tool (the Rholang module) lives separately and needs the elaborator
fully implemented.

This is its own library target so the core `MeTTaIL` library ships without test code.
-/
import MeTTaIL.Theory.Elaborate
import MeTTaILTests.Rholang

namespace MeTTaILTests
open MeTTaIL

private def ctx0 : ElabCtx := {}

private def catA : Cat := .idCat "A"
private def ruleA : Rule := { label := .id "MkA", cat := catA, items := [.terminal "a"] }

/-- Build `{A}`: the sort `A` with one nullary constructor, via
    `addTerms (addExports empty [base A]) [ruleA]`. -/
private def instA : TheoryInst :=
  .addTerms (.addExports .empty [.base catA]) [ruleA]

/-- The presentation `instA` should elaborate to. -/
private def presA : Presentation := .mk [catA] [ruleA] [] [] []

-- `empty` elaborates to the empty presentation.
example : elaborate ctx0 TheoryInst.empty = Except.ok Presentation.empty := rfl

-- A single sort plus constructor elaborates as expected.
example : ((elaborate ctx0 instA).toOption == some presA) = true := by decide

-- Union of a presentation with itself is itself (`distinct` drops the duplicates).
example : ((elaborate ctx0 (.disj instA instA)).toOption == some presA) = true := by decide

-- Intersection of a presentation with itself is itself.
example : ((elaborate ctx0 (.conj instA instA)).toOption == some presA) = true := by decide

-- Difference of a presentation with itself is empty.
example :
    ((elaborate ctx0 (.subtract instA instA)).toOption == some Presentation.empty) = true := by
  decide

-- `let x = instA in x` returns `instA`'s presentation.
example : ((elaborate ctx0 (.letIn "x" instA (.ref "x"))).toOption == some presA) = true := by
  decide

-- A reference to an unbound name is an error.
example : (elaborate ctx0 (.ref "x")).toOption = none := rfl

-- A duplicate label in `addTerms` is rejected.
example : (elaborate ctx0 (.addTerms instA [ruleA])).toOption = none := rfl

end MeTTaILTests
