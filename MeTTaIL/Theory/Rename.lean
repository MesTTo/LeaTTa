/-
Category renaming and constructor relabeling, the traversals behind `addExports` rename and
`addReplacements`.

A `RenameExport old new` renames a sort `old` to `new` everywhere it occurs in the presentation (the
correct rename; the section note records where Scala's buggy `RenameExport` differs, and
`MeTTaIL/HYPERON_IMPROVEMENTS.md` lists those bugs for upstream). A `Replacement [perm] target . cat =>
newDef` swaps the rule labelled `target` for `newDef` and, in every equation and rewrite, relabels each
applied `target` to `newDef`'s label while permuting its arguments by `perm` (Scala `updateAST`).

The traversals over `Cat` and `AST` are hand-written by mutual recursion because both nest through
`List` (`prod` and `sexp`), which structural recursion handles in definitions but `deriving` does
not.
-/
import MeTTaIL.Theory.Instance

namespace MeTTaIL

/-! ### Category replacement (sort renaming)

This is the CORRECT sort rename: replace the generating sort `old` by `new` everywhere it occurs, the
exports, every rule's output sort (only where it mentions `old`), the item sorts (recursing into the
compound sorts `arrow`/`prod`/`listOf` and into abstraction bodies), the sorts carried by list labels,
and the list-label sorts inside equations and rewrites.

Scala `handleAddExports`'s `RenameExport` branch is buggy in ways we deliberately do NOT reproduce; the
formalization does the correct thing and the bugs are recorded for upstream in
`MeTTaIL/HYPERON_IMPROVEMENTS.md`. In short: `updateDef` sets every rule's output sort to `new`
unconditionally, `replaceCats` and the export map are shallow (they miss a sort nested in a compound
sort), and the rename touches only `listcat_`/`listdef_`, leaving stale list-label sorts in rule
labels, equations, and rewrites. The Rholang oracle is unaffected because its one rename is flat
(`Elem -> Proc`, on a presentation whose every rule already has output sort `Elem`, no compound sorts
or list labels), so the correct and buggy renames coincide there.
-/

mutual
  /-- Replace every occurrence of the category `old` by `new` inside a category, recursing into the
      compound sorts. -/
  def Cat.replace (old new : Cat) : Cat → Cat
    | .idCat n   => if Cat.beq (.idCat n) old then new else .idCat n
    | .listOf a  => if Cat.beq (.listOf a) old then new else .listOf (Cat.replace old new a)
    | .arrow a b =>
        if Cat.beq (.arrow a b) old then new
        else .arrow (Cat.replace old new a) (Cat.replace old new b)
    | .prod cs   => if Cat.beq (.prod cs) old then new else .prod (Cat.replaceList old new cs)
  /-- Replace `old` by `new` in each category of a list. -/
  def Cat.replaceList (old new : Cat) : List Cat → List Cat
    | []      => []
    | c :: cs => Cat.replace old new c :: Cat.replaceList old new cs
end

/-- Rename a sort inside a label's category (only list labels carry one). -/
def Label.replaceCat (old new : Cat) : Label → Label
  | .id n       => .id n
  | .wild       => .wild
  | .listE c    => .listE (Cat.replace old new c)
  | .listCons c => .listCons (Cat.replace old new c)
  | .listOne c  => .listOne (Cat.replace old new c)

/-- Rename a sort inside an item, recursing into abstraction bodies. -/
def Item.replaceCat (old new : Cat) : Item → Item
  | .terminal s        => .terminal s
  | .nterminal c       => .nterminal (Cat.replace old new c)
  | .absNTerminal x it => .absNTerminal x (Item.replaceCat old new it)
  | .bindNTerminal x c => .bindNTerminal x (Cat.replace old new c)

/-- Rename a sort throughout a function symbol: its output sort (only when it mentions `old`), its
    label, and its items. Scala `updateDef` instead sets the output sort to `new` unconditionally and
    leaves the label untouched; see `HYPERON_IMPROVEMENTS.md`. -/
def Rule.replaceCat (old new : Cat) (r : Rule) : Rule :=
  { label := r.label.replaceCat old new
    cat := Cat.replace old new r.cat
    items := r.items.map (Item.replaceCat old new) }

mutual
  /-- Rename a sort inside a term (it can appear inside a list label). -/
  def AST.replaceCat (old new : Cat) : AST → AST
    | .var p       => .var p
    | .sexp l args => .sexp (l.replaceCat old new) (AST.replaceCatList old new args)
    | .subst b r v => .subst (AST.replaceCat old new b) (AST.replaceCat old new r) v
  /-- Rename a sort in each term of a list. -/
  def AST.replaceCatList (old new : Cat) : List AST → List AST
    | []      => []
    | a :: as => AST.replaceCat old new a :: AST.replaceCatList old new as
end

/-- Rename a sort inside an equation (reaching the list-label sorts in its terms). -/
def Equation.replaceCat (old new : Cat) : Equation → Equation
  | .impl l r    => .impl (l.replaceCat old new) (r.replaceCat old new)
  | .fresh x y e => .fresh x y (Equation.replaceCat old new e)

/-- Rename a sort inside a rewrite. -/
def Rewrite.replaceCat (old new : Cat) : Rewrite → Rewrite
  | .base l r => .base (l.replaceCat old new) (r.replaceCat old new)
  | .ctx h r  => .ctx h (Rewrite.replaceCat old new r)

/-- Rename a sort inside a named rewrite. -/
def RewriteDecl.replaceCat (old new : Cat) (rd : RewriteDecl) : RewriteDecl :=
  { rd with rw := rd.rw.replaceCat old new }

/-- Rename a sort everywhere in a presentation: exports, function-symbol definitions, and the
    list-label sorts in equations and rewrites. References are left untouched (elaborated presentations
    have none). This is the correct rename; Scala `RenameExport` updates only `listcat_`/`listdef_`, and
    buggily, see `HYPERON_IMPROVEMENTS.md`. -/
def Presentation.replaceCat (old new : Cat) (p : Presentation) : Presentation :=
  .mk (Cat.replaceList old new p.exports)
      (p.terms.map (Rule.replaceCat old new))
      (p.equations.map (Equation.replaceCat old new))
      (p.rewrites.map (RewriteDecl.replaceCat old new))
      p.references

/-! ### Constructor relabeling with argument permutation -/

mutual
  /-- Relabel every applied `oldL` to `newL` in a term, permuting the arguments of each such
      application by `perm` (new position `i` takes old argument `perm[i]`). Children are relabeled
      first. -/
  def AST.relabel (oldL newL : Label) (perm : List Nat) : AST → AST
    | .var p       => .var p
    | .sexp l args =>
        let args' := AST.relabelList oldL newL perm args
        if l == oldL then .sexp newL (perm.filterMap (fun i => args'[i]?))
        else .sexp l args'
    | .subst b r v => .subst (AST.relabel oldL newL perm b) (AST.relabel oldL newL perm r) v
  /-- Relabel each term of a list. -/
  def AST.relabelList (oldL newL : Label) (perm : List Nat) : List AST → List AST
    | []      => []
    | a :: as => AST.relabel oldL newL perm a :: AST.relabelList oldL newL perm as
end

/-- Relabel inside an equation. -/
def Equation.relabel (oldL newL : Label) (perm : List Nat) : Equation → Equation
  | .impl l r    => .impl (l.relabel oldL newL perm) (r.relabel oldL newL perm)
  | .fresh x y e => .fresh x y (Equation.relabel oldL newL perm e)

/-- Relabel inside a rewrite. -/
def Rewrite.relabel (oldL newL : Label) (perm : List Nat) : Rewrite → Rewrite
  | .base l r => .base (l.relabel oldL newL perm) (r.relabel oldL newL perm)
  | .ctx h r  => .ctx h (Rewrite.relabel oldL newL perm r)

/-- Relabel inside a named rewrite. -/
def RewriteDecl.relabel (oldL newL : Label) (perm : List Nat) (rd : RewriteDecl) : RewriteDecl :=
  { rd with rw := rd.rw.relabel oldL newL perm }

/-- Apply one replacement to a presentation: swap the rule labelled `target` for `newDef`, and
    relabel `target` to `newDef`'s label (permuting arguments by `perm`) in every equation and
    rewrite. Mirrors `handleAddReplacements`. -/
def Presentation.applyReplacement (rep : Replacement) (p : Presentation) : Presentation :=
  let oldL := rep.target
  let newL := rep.newDef.label
  .mk p.exports
      (p.terms.map (fun r => if r.label == oldL then rep.newDef else r))
      (p.equations.map (Equation.relabel oldL newL rep.perm))
      (p.rewrites.map (RewriteDecl.relabel oldL newL rep.perm))
      p.references

end MeTTaIL
