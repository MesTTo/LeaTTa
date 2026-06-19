/-
The elaboration interpreter: evaluate a theory instance to a presentation, or fail with an error.

Mirrors the checked `InstInterpreter.interpret` (which runs `check_interpret` then `interpret`). This
file implements the binding, extension, and lattice operations; the operations needing the category
rename/permutation traversals and module resolution are stubbed with explicit errors and tracked
separately, so nothing is silently wrong.
-/
import MeTTaIL.Theory.Instance
import MeTTaIL.Theory.Ops

namespace MeTTaIL

/-- The elaboration context: the modules in scope (for resolving `ctor` and `free`) and the current
    variable environment (let- and parameter-bindings). The last binding for a name wins, matching
    the Scala `env.reverse.find`. -/
structure ElabCtx where
  modules : List Module := []
  env : List (String × Presentation) := []

/-- The first label that occurs more than once in a list of rules, if any. The analogue of the
    Scala duplicate-label check in `checkAddTerms`. -/
def firstDupLabel : List Rule → List Label → Option Label
  | [], _ => none
  | r :: rs, seen =>
      if seen.contains r.label then some r.label else firstDupLabel rs (r.label :: seen)

/-- Render a label for an error message (just its identifier for the common `Id` case). -/
def Label.name : Label → String
  | .id n => n
  | .wild => "_"
  | .listE _ => "[]"
  | .listCons _ => "(:)"
  | .listOne _ => "(:[])"

/-- Elaborate a theory instance to a presentation, or fail with an error message. Mirrors the
    checked `InstInterpreter.interpret`.

    Implemented: `empty`, `ref`, `letIn`, `addExports` (base exports), `addTerms` (with the
    duplicate-label check), `addEquations`, `addRewrites`, and the lattice ops `conj`/`disj`/
    `subtract`.

    Stubbed with explicit errors (tracked): `addExports` rename and `addReplacements` (need the
    category-rename and argument-permutation traversals), and `ctor`/`free` (need module
    resolution). The deeper equation/rewrite category checks (`AddEqRwHelpers`) are also pending; the
    workers here append after only the structural checks above. -/
def elaborate (ctx : ElabCtx) : TheoryInst → Except String Presentation
  | .empty => .ok .empty
  | .ref name =>
      match (ctx.env.reverse).find? (fun b => b.1 == name) with
      | some (_, p) => .ok p
      | none => .error s!"Identifier {name} is free"
  | .letIn name val body => do
      let p ← elaborate ctx val
      elaborate { ctx with env := ctx.env ++ [(name, p)] } body
  | .addTerms base grammar => do
      let p ← elaborate ctx base
      match firstDupLabel (p.terms ++ grammar) [] with
      | some l => .error s!"Duplicate label in addTerms: {l.name}"
      | none => .ok (.mk p.exports (p.terms ++ grammar) p.equations p.rewrites p.references)
  | .addEquations base eqs => do
      let p ← elaborate ctx base
      .ok (.mk p.exports p.terms (p.equations ++ eqs) p.rewrites p.references)
  | .addRewrites base rws => do
      let p ← elaborate ctx base
      .ok (.mk p.exports p.terms p.equations (p.rewrites ++ rws) p.references)
  | .addExports base exps => do
      let p ← elaborate ctx base
      if exps.isEmpty then
        .error "Error: missing distinguished export."
      else
        exps.foldlM
          (fun pp e =>
            match e with
            | .base c => .ok (.mk (pp.exports ++ [c]) pp.terms pp.equations pp.rewrites pp.references)
            | .rename _ _ => .error "addExports rename: not yet implemented")
          p
  | .addReplacements _ _ => .error "addReplacements: not yet implemented"
  | .conj a b => do
      let pa ← elaborate ctx a
      let pb ← elaborate ctx b
      .ok (Presentation.inter pa pb)
  | .disj a b => do
      let pa ← elaborate ctx a
      let pb ← elaborate ctx b
      .ok (Presentation.union pa pb)
  | .subtract a b => do
      let pa ← elaborate ctx a
      let pb ← elaborate ctx b
      .ok (Presentation.diff pa pb)
  | .ctor _ _ => .error "ctor: not yet implemented"
  | .free _ => .error "free: not yet implemented"

end MeTTaIL
