/-
Pure operations on presentations: the helpers the elaborator uses, and the three presentation
lattice operators (union, intersection, difference).

These mirror the Scala `handleDisj`/`handleConj`/`handleSubtract` and the small accessors in
`ASTHelpers`/`LabelHelpers`. They follow the Scala behavior, including its quirks. Two to keep in
mind. Category collection for the intersection and difference filters counts only plain non-terminal
sorts (Scala's `collect { case nt: NTerminal => nt.cat_ }`), not binder items. And `labelsInAST`,
which reads the head label of a term, is non-recursive (though `labelsInEquation` does recurse through
a freshness guard).

One representation difference: the lattice operators keep list order and use `List.contains` with
`distinct`, where Scala uses unordered `Set`s. The results agree as sets, which is what the
presentation comparison and the Rholang oracle rely on.
-/
import MeTTaIL.Syntax

namespace MeTTaIL

/-- Keep the first occurrence of each element, dropping later duplicates. The analogue of Scala
    `List.distinct`. -/
def distinct {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Whether an item is a terminal (a literal token). -/
def Item.isTerminal : Item → Bool
  | .terminal _ => true
  | _           => false

/-- The non-terminal items of a rule: everything that is not a literal token, so plain non-terminals
    and the two binder forms. Mirrors Scala `AddEqRwHelpers.nonTerminals`, used for the arity and
    category-alignment checks on replacements. -/
def Rule.nonTerminalItems (r : Rule) : List Item :=
  r.items.filter (fun i => !i.isTerminal)

/-- The sort of a plain non-terminal item, and nothing for a terminal or a binder. This is the
    category Scala collects with `collect { case nt: NTerminal => nt.cat_ }` in `handleConj`,
    `handleSubtract`, and `checkAddTerms`; binder items are deliberately not counted, matching Scala. -/
def Item.cats : Item → List Cat
  | .nterminal c => [c]
  | _            => []

/-- The categories a function symbol mentions for the intersection and difference filters and the
    unknown-category check: its output sort and the sorts of its plain non-terminal items. Mirrors the
    set `Set(rule.cat_) ++ {nterminal item cats}` Scala builds in `handleConj`, `handleSubtract`, and
    `checkAddTerms`. -/
def Rule.mentionedCats (r : Rule) : List Cat :=
  r.cat :: r.items.flatMap Item.cats

/-- The head label of a term, if it is an applied constructor; nothing for a variable or a
    substitution. -/
def AST.topLabels : AST → List Label
  | .var _ => []
  | .sexp l _ => [l]
  | .subst _ _ _ => []

/-- The (top-level) labels appearing in an equation. Mirrors Scala `labelsInEquation`: it recurses
    through a freshness guard, and on each side takes only the head label (Scala's per-term
    `labelsInAST` is non-recursive). -/
def Equation.labels : Equation → List Label
  | .impl l r => l.topLabels ++ r.topLabels
  | .fresh _ _ e => Equation.labels e

/-- Strip the premises (`let h in ...`) of a rewrite to its conclusion `lhs ~> rhs`. Mirrors
    `ASTHelpers.rewriteBase`. -/
def Rewrite.conclusion : Rewrite → AST × AST
  | .base l r => (l, r)
  | .ctx _ r => Rewrite.conclusion r

/-- The (top-level) labels appearing in a rewrite's conclusion. -/
def RewriteDecl.labels (rd : RewriteDecl) : List Label :=
  let (l, r) := rd.rw.conclusion
  l.topLabels ++ r.topLabels

/-- Union of two presentations: concatenate each component and keep first occurrences. Mirrors
    `handleDisj` (the `\/` operator). -/
def Presentation.union (pa pb : Presentation) : Presentation :=
  .mk (distinct (pa.exports ++ pb.exports))
      (distinct (pa.terms ++ pb.terms))
      (distinct (pa.equations ++ pb.equations))
      (distinct (pa.rewrites ++ pb.rewrites))
      (distinct (pa.references ++ pb.references))

/-- Intersection of two presentations, filtered to common sorts and surviving labels. Mirrors
    `handleConj` (the `/\` operator): keep sorts in both; keep defs in both whose mentioned
    categories are all common; keep equations/rewrites in both whose labels all survive. -/
def Presentation.inter (pa pb : Presentation) : Presentation :=
  let commonCats := pa.exports.filter (fun c => pb.exports.contains c)
  let defs := (pa.terms.filter (fun d => pb.terms.contains d)).filter
                (fun d => d.mentionedCats.all (fun c => commonCats.contains c))
  let labels := defs.map (·.label)
  let eqs := (pa.equations.filter (fun e => pb.equations.contains e)).filter
                (fun e => e.labels.all (fun l => labels.contains l))
  let rws := (pa.rewrites.filter (fun r => pb.rewrites.contains r)).filter
                (fun r => r.labels.all (fun l => labels.contains l))
  .mk commonCats defs eqs rws []

/-- Difference of two presentations. Mirrors `handleSubtract` (the `\` operator): remove `pb`'s
    sorts; drop defs that are in `pb` or that mention a removed sort; keep equations/rewrites not in
    `pb` whose labels all survive. -/
def Presentation.diff (pa pb : Presentation) : Presentation :=
  let removed := pa.exports.filter (fun c => pb.exports.contains c)
  let cats := pa.exports.filter (fun c => !pb.exports.contains c)
  let defs := pa.terms.filter
                (fun d => !pb.terms.contains d && d.mentionedCats.all (fun c => !removed.contains c))
  let labels := defs.map (·.label)
  let eqs := (pa.equations.filter (fun e => !pb.equations.contains e)).filter
                (fun e => e.labels.all (fun l => labels.contains l))
  let rws := (pa.rewrites.filter (fun r => !pb.rewrites.contains r)).filter
                (fun r => r.labels.all (fun l => labels.contains l))
  .mk cats defs eqs rws []

/-- The base identifier of a dotted path: the variable name it heads. A premise `src ~> tgt` binds
    `tgt`'s base identifier. -/
def DottedPath.baseName : DottedPath → String
  | .base n => n
  | .qualified n _ => n

/-- The premises (the `let h in ...` hypotheses) of a rewrite, outermost first. -/
def Rewrite.premises : Rewrite → List Hyp
  | .base _ _ => []
  | .ctx h r => h :: Rewrite.premises r

end MeTTaIL
