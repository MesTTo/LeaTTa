-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Transform.Desugar
Layer: Transform
Purpose: The DesugarBinds pass. After each rule that binds a variable, it adds a `...ToArrow` companion
  whose higher-order argument is written as an arrow. Mirrors the Scala `DesugarBinds`
  (`mangleBindLabel`, `addDesugaredLambdas`). The type-lift pass needs this form because it skips rules
  with raw binders. Example (from the Rholang module): `PNew . Proc ::= "new" (Bind x Name) "in" (x)
  Proc` gains `PNewToArrow . Proc ::= "PNewToArrow" "(" (Name -> Proc) ")"`.
Imports: MeTTaIL.Syntax
Trusted boundary: none
Main exports: bindEnv, Item.argCat, desugarArgs, Rule.hasBind, Rule.toArrow, desugarBinds
Open obligations: none
-/
import MeTTaIL.Syntax

namespace MeTTaIL

/-- The binder-name to category bindings recorded by a rule's `Bind` items. -/
def bindEnv (items : List Item) : List (String × Cat) :=
  items.filterMap (fun it => match it with | .bindNTerminal x c => some (x, c) | _ => none)

/-- The argument category an item denotes after desugaring: a plain non-terminal keeps its category;
    an abstraction `(x) body` becomes `arrow (type of x) (body's category)`, right-nested for a chain
    of abstractions. Terminals and binders carry no argument category. -/
def Item.argCat (env : List (String × Cat)) : Item → Option Cat
  | .nterminal c => some c
  | .absNTerminal x inner =>
      match (env.find? (fun p => p.1 == x)).map (·.2), Item.argCat env inner with
      | some dom, some cod => some (.arrow dom cod)
      | _, _ => none
  | _ => none

/-- The non-terminal arguments of a rule after desugaring binders: keep plain non-terminals, turn
    abstractions into arrows (using the binder types), drop binders and terminals. -/
def desugarArgs (env : List (String × Cat)) (items : List Item) : List Item :=
  items.filterMap fun it =>
    match it with
    | .nterminal c => some (.nterminal c)
    | .absNTerminal x inner => (Item.argCat env (.absNTerminal x inner)).map Item.nterminal
    | _ => none

/-- Whether a rule binds a variable (has a `Bind` item). -/
def Rule.hasBind (r : Rule) : Bool :=
  r.items.any fun it => match it with | .bindNTerminal _ _ => true | _ => false

/-- The `...ToArrow` companion of a rule that binds variables: function-style syntax whose arguments
    are the desugared non-terminals. -/
def Rule.toArrow (r : Rule) : Rule :=
  let env := bindEnv r.items
  let baseName := match r.label with | .id n => n | _ => ""
  let arrowName := baseName ++ "ToArrow"
  { label := .id arrowName, cat := r.cat
    items := .terminal arrowName :: .terminal "(" :: desugarArgs env r.items ++ [.terminal ")"] }

/-- The DesugarBinds pass: after each rule that binds a variable, insert its `...ToArrow` companion.
    Rules without binders are left unchanged, in place. -/
def desugarBinds (p : Presentation) : Presentation :=
  .mk p.exports
      (p.terms.flatMap fun r => if r.hasBind then [r, r.toArrow] else [r])
      p.equations p.rewrites p.references

end MeTTaIL
