/-
Category renaming and constructor relabeling, the traversals behind `addExports` rename and
`addReplacements`.

A `RenameExport old new` renames a sort in the exported sort list and in the function-symbol
definitions, mirroring Scala `handleAddExports`'s `RenameExport` branch (it updates `listcat_` and
`listdef_` only, leaving equations and rewrites untouched). The section note below flags the two Scala
quirks this reproduces. A `Replacement [perm] target . cat => newDef` swaps the rule labelled `target`
for `newDef` and, in every equation and rewrite, relabels each applied `target` to `newDef`'s label
while permuting its arguments by `perm` (Scala `updateAST`).

The traversals over `Cat` and `AST` are hand-written by mutual recursion because both nest through
`List` (`prod` and `sexp`), which structural recursion handles in definitions but `deriving` does
not.
-/
import MeTTaIL.Theory.Instance

namespace MeTTaIL

/-! ### Category replacement (sort renaming)

The `addExports` sort rename, mirroring Scala `handleAddExports`'s `RenameExport` branch, including its
quirks. Two to flag.

The export list is renamed by a shallow conditional map: a sort equal to `old` becomes `new`, the rest
are left alone (Scala `currentCats.map(c => if c == re.cat_1 then re.cat_2 else c)`). It does not
descend into a compound sort, so `old` nested inside an `arrow`/`prod`/`listOf` export is not renamed.

The function symbols are renamed by `updateDef`, which has a real bug we reproduce to stay faithful to
the tool: it sets every rule's output sort to `new` UNCONDITIONALLY (Scala `new Rule(rule.label_,
newCat, ...)` in `ASTHelpers.scala`), not only the rules whose output sort was `old`. On a presentation
with mixed output sorts this corrupts the others. It is masked in the tested modules because the one
rename acts on a presentation whose every rule already has output sort `old`. The rule's label is left
unchanged, and its items get a shallow per-item replace (a non-terminal or binder sort equal to `old`
becomes `new`, an abstraction is followed into its body, but a sort is compared as a whole). Flagged
for F1R3FLY.
-/

/-- Shallow per-item sort replace, mirroring Scala `ASTHelpers.replaceCats`: a non-terminal or binder
    whose sort equals `old` becomes `new`; an abstraction is followed into its body; a sort is compared
    as a whole, so `old` nested inside a compound sort is not replaced. -/
def Item.replaceCat (old new : Cat) : Item → Item
  | .terminal s        => .terminal s
  | .nterminal c       => if Cat.beq c old then .nterminal new else .nterminal c
  | .absNTerminal x it => .absNTerminal x (Item.replaceCat old new it)
  | .bindNTerminal x c => if Cat.beq c old then .bindNTerminal x new else .bindNTerminal x c

/-- Rename a sort in one function symbol, mirroring Scala `updateDef`: the output sort is set to `new`
    UNCONDITIONALLY (the Scala bug noted above), the label is left unchanged, and the items get the
    shallow per-item replace. -/
def Rule.replaceCat (old new : Cat) (r : Rule) : Rule :=
  { r with cat := new, items := r.items.map (Item.replaceCat old new) }

/-- Rename a sort in a presentation's exported sort list and its function-symbol definitions, leaving
    equations, rewrites, and references untouched. Mirrors Scala `handleAddExports`'s `RenameExport`
    branch, which updates `listcat_` and `listdef_` only (see the section note for the shallow-map and
    `updateDef` quirks it reproduces). -/
def Presentation.replaceCat (old new : Cat) (p : Presentation) : Presentation :=
  .mk (p.exports.map (fun c => if Cat.beq c old then new else c))
      (p.terms.map (Rule.replaceCat old new))
      p.equations
      p.rewrites
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
