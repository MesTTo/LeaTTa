/-
The theory-instance algebra: the expression language whose elaboration produces a `Presentation`.

Mirrors the Scala `TheoryInst` family (the cases `InstInterpreter.interpret` dispatches) and the
declaration layer (`TheoryDecl`, `VariableDecl`, `Module`) used to resolve `ctor` and `free`. A
`.module` file is a program in this algebra; the last `theory INST` in a module is its entry point.
-/
import MeTTaIL.Syntax

namespace MeTTaIL

/-- An export clause inside `Exports { ... }`. `base c` adds the sort `c`; `rename old new` renames
    an inherited sort everywhere. Mirrors BNFC `Export` (`BaseExport | RenameExport`). -/
inductive Export where
  | base (c : Cat)
  | rename (old new : Cat)
deriving Inhabited, BEq

/-- A replacement clause `[perm] target . cat => newDef` inside `Replacements { ... }`: replace the
    rule labelled `target` of output sort `cat` by `newDef`, applying the argument permutation `perm`
    when propagating the relabel through equations and rewrites. Mirrors BNFC
    `SimpleRepl . Replacement ::= IntList Label "." Cat "=>" Def`. -/
structure Replacement where
  perm : List Nat
  target : Label
  cat : Cat
  newDef : Rule
deriving Inhabited, BEq

/-- A theory parameter declaration `ident : theoryType`. Mirrors BNFC `VarDecl . VariableDecl`. -/
structure VarDecl where
  ident : String
  theoryType : DottedPath
deriving Inhabited, BEq

/-- The theory-instance algebra. These are exactly the forms `InstInterpreter.interpret` handles:
    the binding forms (`empty`, `ref`, `letIn`, `ctor`, `free`), the extension forms (`addExports`,
    `addReplacements`, `addTerms`, `addEquations`, `addRewrites`), and the presentation-lattice
    operators (`conj` = intersection `/\`, `disj` = union `\/`, `subtract` = difference `\`).

    `letIn name val body` is `let name = val in (body)`. The constructor is named `letIn` rather than
    `rec` because every inductive already has an auto-generated `TheoryInst.rec`. -/
inductive TheoryInst where
  | empty
  | ref (name : String)
  | letIn (name : String) (val : TheoryInst) (body : TheoryInst)
  | ctor (path : DottedPath) (args : List TheoryInst)
  | free (path : DottedPath)
  | addExports (base : TheoryInst) (exports : List Export)
  | addReplacements (base : TheoryInst) (repls : List Replacement)
  | addTerms (base : TheoryInst) (grammar : List Rule)
  | addEquations (base : TheoryInst) (eqs : List Equation)
  | addRewrites (base : TheoryInst) (rws : List RewriteDecl)
  | conj (a b : TheoryInst)
  | disj (a b : TheoryInst)
  | subtract (a b : TheoryInst)
deriving Inhabited

/-- A theory declaration `Theory name(params) { body }`. Mirrors BNFC `BaseTheoryDecl`. -/
structure TheoryDecl where
  name : String
  params : List VarDecl
  body : TheoryInst
deriving Inhabited

/-- A module: a named collection of theory declarations. Imports are resolved at a higher layer; for
    elaboration what matters is the set of theory declarations in scope. Mirrors BNFC `ModuleImpl`
    restricted to its theory declarations. -/
structure Module where
  name : String
  theories : List TheoryDecl
deriving Inhabited

/-- Look up a theory declaration by name in a module. -/
def Module.find? (m : Module) (name : String) : Option TheoryDecl :=
  m.theories.find? (fun d => d.name == name)

end MeTTaIL
