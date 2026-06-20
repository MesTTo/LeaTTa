# MeTTaIL improvements for F1R3FLY

Findings about the MeTTaIL tool, collected while building the Lean 4 formalization in this directory.
Each one is a place where the Scala implementation does something that looks wrong. The Lean model
does the correct thing instead and leaves a comment at the divergence pointing back here, so the
formalization is not bug-for-bug with the tool. None of these are exercised by the `Rholang.module`
example we cross-check against, which is why the tool still produces the right output there and our
oracle still matches it.

Paths are relative to the MeTTaIL repository
(`MeTTaIL/src/main/scala/io/f1r3fly/mettail/`). Line numbers are approximate; method names are exact.

This file is meant to be added to as more findings turn up.

## 1. `updateDef` rewrites every rule's output sort on a rename

`ASTHelpers.updateDef` (~L47), called from `InstInterpreterCases.handleAddExports` (~L256) for every
definition.

```scala
def updateDef(d: Def, oldCat: Cat, newCat: Cat): Def = d match {
  case rule: Rule => new Rule(rule.label_, newCat, replaceCats(oldCat, newCat, rule.listitem_))
}
```

The output sort is set to `newCat` unconditionally. `handleAddExports` maps this over every rule, so a
`RenameExport old new` sets the output sort of *every* rule to `new`, not only the rules whose output
sort was `old`. On a presentation with more than one sort this corrupts all the rules whose output sort
is not the renamed one.

Correct behavior: rename the output sort only where it mentions `old`. Our `Rule.replaceCat` in
`MeTTaIL/Theory/Rename.lean` uses a conditional replace.

Masked in the example: the Rholang rename `Elem -> Proc` runs on a sub-presentation whose only two
rules already have output sort `Elem`, so unconditional and conditional agree there.

## 2. The export rename is shallow

`ASTHelpers.replaceCats` (~L30) and the export-list map in `handleAddExports` (~L255):

```scala
currentCats.map(c => if (c == re.cat_1) re.cat_2 else c)
```

Both compare a sort to `old` as a whole and replace only on a top-level match. Neither descends into a
compound sort. So renaming `Proc -> Q` leaves an export or argument sort `Name -> Proc` unchanged,
because `Name -> Proc` is not equal to `Proc`. After the rename, compound sorts still name the old
sort.

Correct behavior: recurse into `arrow`, `prod`, and `listOf` when renaming. Our `Cat.replace` recurses.

Masked in the example: Rholang's sorts are all flat `IdCat`s, so there is nothing nested to miss.

## 3. The rename skips equations, rewrites, and rule labels

`handleAddExports` (~L256) rebuilds the presentation with `copyPres(..., listcat = ..., listdef =
...)`, touching only `listcat_` and `listdef_`. `updateDef` also leaves `rule.label_` unchanged.

A sort can appear inside a list label (`[]{cat}`, `(:){cat}`, `(:[]){cat}`): in a rule's label and in
the terms of equations and rewrites. A rename that updates only the export list and the rule arities
leaves those occurrences pointing at the old sort.

Correct behavior: rename the list-label sorts in rule labels, equations, and rewrites too. Our
`Presentation.replaceCat` renames all of them.

Masked in the example: Rholang uses only `Id` labels, so there are no list-label sorts anywhere.

## 4. `checkAddExports` checks only the first export and rejects a leading base export

`InstInterpreterCases.checkAddExports` (~L222):

```scala
inst.listexport_.toArray.toList.collectFirst {
  case re: RenameExport => if (!currentCats.exists(_.equals(re.cat_1))) Some("...not found...") else None
  case _                => Some("Error: Unknown export type encountered in addExports.")
}.flatten
```

`collectFirst` applies the partial function to the first element for which it is defined. This partial
function is defined for every export (the `case _`), so `collectFirst` only ever inspects the *first*
export. Two consequences:

- A second or later `RenameExport` whose target sort is missing is not caught at check time.
- If the first export is a `BaseExport`, the `case _` arm fires and the whole `addExports` is rejected
  with "Unknown export type encountered", even though adding a base export is legal.

Correct behavior: fold over all exports, adding base exports and checking each rename's target. Our
elaborator (`MeTTaIL/Theory/Elaborate.lean`, the `addExports` case) does this.

Masked in the example: this checker is never reached for the Rholang `addExports` nodes, because of
finding 5.

## 5. `check_interpret` does not recurse through `let`, union, intersection, or difference

`InstInterpreter.check_interpret` (~L35):

```scala
case disj: TheoryInstDisj     => None
case conj: TheoryInstConj     => None
case subtract: TheoryInstSubtract => None
...
case rec: TheoryInstRec       => None   // the `let ... in ...` form
```

The static check returns `None` for these forms without inspecting their sub-instances; only `ctor`
and `free` recurse, and the `addX` cases check just their own node. So a malformed instance nested
under a `let`, `\/`, `/\`, or `\` is never checked. The error, if any, only surfaces during
`interpret`, or not at all.

Correct behavior: recurse into the sub-instances of `let`/union/intersection/difference. Our elaborator
checks every node as it elaborates it, so it catches these.

Masked in the example: the Rholang module's `addExports`/`addTerms`/`addReplacements` nodes all sit
under a `let` chain, so `check_interpret` never reaches them. The tool still produces the right output
because the module is well formed and `interpret` does the work.
