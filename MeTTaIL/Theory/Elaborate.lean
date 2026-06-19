/-
The elaboration interpreter: evaluate a theory instance to a presentation, or fail with an error.

Mirrors the checked `InstInterpreter.interpret` (which runs `check_interpret` then `interpret`).
`ctor` and `free` expand another theory's body, so elaboration is not structural on the theory
instance; it is bounded by fuel, matching the fuel-bounded interpreters elsewhere in this repository
and keeping the development free of `partial`.
-/
import MeTTaIL.Theory.Instance
import MeTTaIL.Theory.Ops
import MeTTaIL.Theory.Rename
import MeTTaIL.Theory.Check

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

/-- Render a label for an error message (its identifier for the common `Id` case). -/
def Label.name : Label → String
  | .id n => n
  | .wild => "_"
  | .listE _ => "[]"
  | .listCons _ => "(:)"
  | .listOne _ => "(:[])"

/-- The final identifier of a dotted path (the theory name; the prefix selects the module). -/
def DottedPath.lastIdent : DottedPath → String
  | .base n => n
  | .qualified _ rest => DottedPath.lastIdent rest

/-- Resolve a dotted path to a theory declaration by its final identifier, searching all modules in
    scope. Theory names are unique across the encoded modules, so the module prefix is not needed to
    disambiguate. Mirrors `ModuleProcessor.resolveDottedPath`. -/
def resolveTheory (modules : List Module) (path : DottedPath) : Except String TheoryDecl :=
  match modules.findSome? (fun m => m.find? path.lastIdent) with
  | some td => .ok td
  | none => .error s!"Theory '{path.lastIdent}' not found"

/-- The default fuel for the public `elaborate`: an upper bound on the number of elaboration steps.
    Reduction cost is proportional to the steps actually taken, not to this bound. -/
def defaultFuel : Nat := 100000

mutual
  /-- Elaborate a theory instance to a presentation under a fuel bound. Mirrors the checked
      `InstInterpreter.interpret`.

      Implemented: `empty`, `ref`, `letIn`, `ctor`, `free` (recursive free-instantiation of a
      theory's parameters), `addExports` (base and rename), `addReplacements` (relabel with argument
      permutation), `addTerms` (with the duplicate-label check), `addEquations`, `addRewrites`, and
      the lattice ops `conj`/`disj`/`subtract`.

      The workers run the category checks (`Theory/Check`: the two sides of each equation and each
      rewrite conclusion have compatible top-level categories, and every rewrite right-hand-side
      variable is bound on the left or by a premise) plus the structural checks (duplicate label,
      missing export, replacement target/shadow). Pending: the deeper per-variable category-consistency
      check (`catOfIdentInAST`, that each variable resolves to a single category). -/
  def elaborateFuel : Nat → ElabCtx → TheoryInst → Except String Presentation
    | 0, _, _ => .error "elaborate: out of fuel"
    | _+1, _, .empty => .ok .empty
    | _+1, ctx, .ref name =>
        match (ctx.env.reverse).find? (fun b => b.1 == name) with
        | some (_, p) => .ok p
        | none => .error s!"Identifier {name} is free"
    | fuel+1, ctx, .letIn name val body => do
        let p ← elaborateFuel fuel ctx val
        elaborateFuel fuel { ctx with env := ctx.env ++ [(name, p)] } body
    | fuel+1, ctx, .addTerms base grammar => do
        let p ← elaborateFuel fuel ctx base
        match firstDupLabel (p.terms ++ grammar) [] with
        | some l => .error s!"Duplicate label in addTerms: {l.name}"
        | none => .ok (.mk p.exports (p.terms ++ grammar) p.equations p.rewrites p.references)
    | fuel+1, ctx, .addEquations base eqs => do
        let p ← elaborateFuel fuel ctx base
        match eqs.findSome? (checkEquation p.terms) with
        | some err => .error err
        | none => .ok (.mk p.exports p.terms (p.equations ++ eqs) p.rewrites p.references)
    | fuel+1, ctx, .addRewrites base rws => do
        let p ← elaborateFuel fuel ctx base
        match rws.findSome? (checkRewrite p.terms) with
        | some err => .error err
        | none => .ok (.mk p.exports p.terms p.equations (p.rewrites ++ rws) p.references)
    | fuel+1, ctx, .addExports base exps => do
        let p ← elaborateFuel fuel ctx base
        if exps.isEmpty then .error "Error: missing distinguished export."
        else
          exps.foldlM
            (fun pp e =>
              match e with
              | .base c =>
                  .ok (.mk (pp.exports ++ [c]) pp.terms pp.equations pp.rewrites pp.references)
              | .rename old new =>
                  if pp.exports.contains old then .ok (Presentation.replaceCat old new pp)
                  else .error "addExports: cannot rename a sort that is not exported")
            p
    | fuel+1, ctx, .addReplacements base reps => do
        let p ← elaborateFuel fuel ctx base
        reps.foldlM
          (fun pp rep =>
            if !(pp.terms.any (fun r => r.label == rep.target)) then
              .error s!"Replacement target {rep.target.name} not found"
            else if pp.terms.any (fun r => r.label == rep.newDef.label) then
              .error s!"Replacement rule label {rep.newDef.label.name} already exists in theory."
            else .ok (Presentation.applyReplacement rep pp))
          p
    | fuel+1, ctx, .conj a b => do
        let pa ← elaborateFuel fuel ctx a
        let pb ← elaborateFuel fuel ctx b
        .ok (Presentation.inter pa pb)
    | fuel+1, ctx, .disj a b => do
        let pa ← elaborateFuel fuel ctx a
        let pb ← elaborateFuel fuel ctx b
        .ok (Presentation.union pa pb)
    | fuel+1, ctx, .subtract a b => do
        let pa ← elaborateFuel fuel ctx a
        let pb ← elaborateFuel fuel ctx b
        .ok (Presentation.diff pa pb)
    | fuel+1, ctx, .ctor path args => do
        let td ← resolveTheory ctx.modules path
        if args.length != td.params.length then
          .error s!"Mismatch in number of arguments to theory {td.name}"
        else do
          let argPres ← elaborateArgs fuel ctx args
          let bindings := (td.params.map (·.ident)).zip argPres
          elaborateFuel fuel { ctx with env := ctx.env ++ bindings } td.body
    | fuel+1, ctx, .free path => do
        let td ← resolveTheory ctx.modules path
        let argPres ← freeArgs fuel ctx (td.params.map (·.theoryType))
        let bindings := (td.params.map (·.ident)).zip argPres
        elaborateFuel fuel { ctx with env := ctx.env ++ bindings } td.body
  /-- Elaborate each theory instance in a list (the actual arguments of a `ctor`). -/
  def elaborateArgs : Nat → ElabCtx → List TheoryInst → Except String (List Presentation)
    | 0, _, _ => .error "elaborate: out of fuel"
    | _+1, _, [] => .ok []
    | fuel+1, ctx, a :: rest => do
        let p ← elaborateFuel fuel ctx a
        let ps ← elaborateArgs fuel ctx rest
        .ok (p :: ps)
  /-- Free-instantiate each parameter's theory type in turn (the recursive instantiation `free`
      performs: every parameter is itself filled by free-instantiating its declared theory). -/
  def freeArgs : Nat → ElabCtx → List DottedPath → Except String (List Presentation)
    | 0, _, _ => .error "elaborate: out of fuel"
    | _+1, _, [] => .ok []
    | fuel+1, ctx, path :: rest => do
        let p ← elaborateFuel fuel ctx (.free path)
        let ps ← freeArgs fuel ctx rest
        .ok (p :: ps)
end

/-- Elaborate a theory instance with the default fuel bound. -/
def elaborate (ctx : ElabCtx) (ti : TheoryInst) : Except String Presentation :=
  elaborateFuel defaultFuel ctx ti

end MeTTaIL
