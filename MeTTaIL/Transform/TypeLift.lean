/-
Module: MeTTaIL.Transform.TypeLift
Layer: Transform
Purpose: The Hypercube type-lift pass (`--hypercube`), the untyped-to-typed transformation of
  `transformation.md`, restricted to the part the Scala tool actually implements. For each function
  symbol it adds a `TypeLiftCC<L>DD` companion (the "type of L") whose arity is the type-lift `T` of the
  original arity: T(G) = G, T(A -> B) = T(A) x (T(A) -> T(B)), T(A x B) = T(A) x T(B), T([A]) = [T(A)].
  Rules with raw binders are skipped (the desugared `...ToArrow` form is lifted instead). After the
  lift, the duplication rule fires: when a variable occurs as a direct argument two or more times across
  the constructor applications in a rewrite's left-hand side, each hosting constructor's companion gains
  an extra argument of that variable's category. The modal possibility types of `transformation.md` are
  not generated here, exactly as in the Scala code (that step is commented out), so the pass is faithful
  to the tool, not to the full design note.
Imports: MeTTaIL.Theory.Ops, MeTTaIL.Transform.Desugar
Trusted boundary: none
Main exports: Cat.typeLift, Rule.hasRawBinder, Rule.argCats, Rule.typeLiftDef, AST.directVarArgs,
  companionLabelOf, extrasForLHS, typeLift
Open obligations: none
-/
import MeTTaIL.Theory.Ops
import MeTTaIL.Transform.Desugar

namespace MeTTaIL

mutual
  /-- The arity type-lift `T`. The arrow case duplicates the domain: one copy for the value, one for
      its type. -/
  def Cat.typeLift : Cat → Cat
    | .idCat n   => .idCat n
    | .arrow s t => .prod [Cat.typeLift s, .arrow (Cat.typeLift s) (Cat.typeLift t)]
    | .prod cs   => .prod (Cat.typeLiftList cs)
    | .listOf a  => .listOf (Cat.typeLift a)
  /-- The type-lift on a list of categories. -/
  def Cat.typeLiftList : List Cat → List Cat
    | []      => []
    | c :: cs => Cat.typeLift c :: Cat.typeLiftList cs
end

/-- Whether an item is a raw binder (a `BindNTerminal` or an `AbsNTerminal`). -/
def Item.isRawBinder : Item → Bool
  | .bindNTerminal _ _ => true
  | .absNTerminal _ _  => true
  | _                  => false

/-- Whether a rule carries a raw binder of either kind. The Scala `--hypercube` pass
    (`Hypercube.scala`) skips such a rule for both `BindNTerminal` and `AbsNTerminal` items, unlike the
    desugar pass, which keys on `BindNTerminal` alone (`Rule.hasBind`). -/
def Rule.hasRawBinder (r : Rule) : Bool := r.items.any Item.isRawBinder

/-- The category of the argument an item contributes in a term: a non-terminal's category, a binder's
    category, or, for an abstraction, the innermost non-abstraction category. `Rule.typeLiftDef` skips
    any rule with a raw binder, so its use of `argCats` sees only binder-free rules. `extrasForLHS` may
    also read `argCats` on a bindered host rule (see `companionLabelOf`), where the `bindNTerminal` arm
    applies. Known divergence there: Scala `optCatFromItem` maps a `BindNTerminal` to `IdCat(name)`, not
    to its category; the tested calculi never index a `BindNTerminal` position with a repeated
    left-hand-side variable, so this arm is unreached here. -/
def Item.bodyCat : Item → Option Cat
  | .terminal _        => none
  | .nterminal c       => some c
  | .bindNTerminal _ c => some c
  | .absNTerminal _ it => Item.bodyCat it

/-- The argument categories of a rule, in the order arguments appear in an applied term. -/
def Rule.argCats (r : Rule) : List Cat := r.items.filterMap Item.bodyCat

/-- The base `TypeLiftCC<L>DD` companion of a rule, or `none` if the rule has raw binders (those are
    lifted only in their desugared `...ToArrow` form). Function-style syntax over the type-lifted
    argument categories. -/
def Rule.typeLiftDef (r : Rule) : Option Rule :=
  if r.hasRawBinder then none
  else
    let baseName := match r.label with | .id n => n | _ => ""
    let lname := "TypeLiftCC" ++ baseName ++ "DD"
    let liftedArgs := r.argCats.map fun c => Item.nterminal (Cat.typeLift c)
    some { label := .id lname, cat := Cat.typeLift r.cat
           items := .terminal lname :: .terminal "(" :: liftedArgs ++ [.terminal ")"] }

/-- The direct variable arguments at one applied constructor: `(name, label, index)` for each
    argument that is a bare variable. -/
def levelVarArgs (l : Label) (args : List AST) : List (String × Label × Nat) :=
  ((List.range args.length).zip args).filterMap fun p =>
    match p.2 with | .var (.base v) => some (v, l, p.1) | _ => none

mutual
  /-- Every direct variable-argument occurrence in a term: which constructor it is an argument of,
      and at which position. -/
  def AST.directVarArgs : AST → List (String × Label × Nat)
    | .var _        => []
    | .sexp l args  => levelVarArgs l args ++ AST.directVarArgsList args
    | .subst b r _  => AST.directVarArgs b ++ AST.directVarArgs r
  /-- Direct variable-argument occurrences across a list of terms. -/
  def AST.directVarArgsList : List AST → List (String × Label × Nat)
    | []      => []
    | a :: as => AST.directVarArgs a ++ AST.directVarArgsList as
end

/-- The companion label a host symbol's extra arguments attach to: the symbol's own companion, or its
    `...ToArrow` companion when the symbol has binders (so its plain companion was skipped). -/
def companionLabelOf (terms : List Rule) (host : Label) : String :=
  let baseName := match host with | .id n => n | _ => ""
  match terms.find? (fun r => r.label == host) with
  | some r => if r.hasRawBinder then "TypeLiftCC" ++ baseName ++ "ToArrowDD"
              else "TypeLiftCC" ++ baseName ++ "DD"
  | none => "TypeLiftCC" ++ baseName ++ "DD"

/-- The extra companion arguments contributed by one rewrite's left-hand side: when a variable occurs
    as a direct argument two or more times across the constructor applications, each hosting
    constructor's companion gains an argument of that variable's category. We count direct-argument
    occurrences, so a variable repeated inside one constructor counts each occurrence; Scala counts
    distinct constructor nodes (`freeVarsInAST` returns a set keyed by structural node equality, so two
    structurally identical hosting constructors collapse to one). The two agree when each repeated
    variable spans distinct, non-identical constructors, as in the comm example. Only base (unqualified)
    variables participate, matching the matcher's variable model. -/
def extrasForLHS (terms : List Rule) (lhs : AST) : List (String × Cat) :=
  let occs := lhs.directVarArgs
  occs.filterMap fun o =>
    let v := o.1; let host := o.2.1; let idx := o.2.2
    if (occs.filter (fun o2 => o2.1 == v)).length ≥ 2 then
      match terms.find? (fun r => r.label == host) with
      | some r => match r.argCats[idx]? with
                  | some c => some (companionLabelOf terms host, c)
                  | none => none
      | none => none
    else none

/-- Append extra argument non-terminals to a companion rule, just before its closing parenthesis. -/
def appendArgs (comp : Rule) (extraCats : List Cat) : Rule :=
  let extraItems := extraCats.map Item.nterminal
  match comp.items.reverse with
  | close :: rest => { comp with items := rest.reverse ++ extraItems ++ [close] }
  | []            => comp

/-- The Hypercube type-lift pass: add the type-lifted companion of every symbol, then apply the
    duplicated-variable extension from the rewrites. The original terms, equations, and rewrites are
    carried through unchanged. -/
def typeLift (p : Presentation) : Presentation :=
  let companions := p.terms.filterMap Rule.typeLiftDef
  let compExtras := p.rewrites.flatMap fun rd => extrasForLHS p.terms rd.rw.conclusion.fst
  let companions' := companions.map fun comp =>
    let myExtras := (compExtras.filter (fun ce => comp.label == .id ce.1)).map (·.2)
    if myExtras.isEmpty then comp else appendArgs comp myExtras
  .mk p.exports (p.terms ++ companions') p.equations p.rewrites p.references

end MeTTaIL
