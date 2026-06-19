/-
Pure operations on presentations: the helpers the elaborator uses, and the three presentation
lattice operators (union, intersection, difference).

These mirror the Scala `handleDisj`/`handleConj`/`handleSubtract` and the small accessors in
`ASTHelpers`/`LabelHelpers`. They are deliberately faithful to the Scala behavior, including its
quirks (for example, `LabelHelpers.labelsInEquation` is non-recursive, so the label extraction here
takes only the head label of each term).
-/
import MeTTaIL.Syntax

namespace MeTTaIL

/-- Keep the first occurrence of each element, dropping later duplicates. The analogue of Scala
    `List.distinct`. -/
def distinct {α : Type} [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The categories an item mentions. -/
def Item.cats : Item → List Cat
  | .terminal _ => []
  | .nterminal c => [c]
  | .absNTerminal _ it => Item.cats it
  | .bindNTerminal _ c => [c]

/-- The categories a label mentions: the element category of a list label, nothing otherwise. -/
def Label.cats : Label → List Cat
  | .id _ | .wild => []
  | .listE c | .listCons c | .listOne c => [c]

/-- Every category a function symbol mentions: its output sort, its label's category, and the
    categories of its items. -/
def Rule.mentionedCats (r : Rule) : List Cat :=
  r.cat :: (r.label.cats ++ r.items.flatMap Item.cats)

/-- The head label of a term, if it is an applied constructor; nothing for a variable or a
    substitution. -/
def AST.topLabels : AST → List Label
  | .var _ => []
  | .sexp l _ => [l]
  | .subst _ _ _ => []

/-- The (top-level) labels appearing in an equation. Mirrors Scala `labelsInEquation`, which is
    deliberately non-recursive: only the head label of each side is taken. -/
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
