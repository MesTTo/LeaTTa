-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Semantics.WellSorted
Layer: Semantics
Purpose: A recursive (all-subterms) sort system for the grammar, deeper than the head-sort discipline of
  `Semantics/Sorts`. A term is well-sorted at a category when it is a variable of that sort in the context,
  or an application `(l a1 ... an)` of a function symbol `l` whose rule has that result category and whose
  arguments are recursively well-sorted at the rule's argument categories (read off the rule's
  non-terminal items by `Item.cats`). The headline is the substitution lemma `inst_wellSorted`:
  instantiating a well-sorted term with a substitution that is well-sorted for the context yields a
  well-sorted term. This is the inst half of the substitution lemma at the heart of subject reduction; the
  matching half (a successful match of a well-sorted term against a well-sorted pattern produces a
  well-sorted substitution) and the full preservation theorem build on it. The system is first-order here
  (variables and applications); binder items and the `Subst` node are out of scope.
Imports: MeTTaIL.Semantics.Reduce (AST.inst), MeTTaIL.Theory.Ops (Item.cats)
Trusted boundary: none (fully proved)
Main exports: Ctx, Rule.argSorts, WellSorted, WellSortedList, inst_wellSorted, instList_wellSorted
Open obligations: the matching half (matchPat against a well-sorted pattern) and the full subject-reduction
  theorem; binder/Subst handling.
-/
import MeTTaIL.Semantics.Reduce
import MeTTaIL.Theory.Ops

namespace MeTTaIL

/-- A typing context: the sort of each free variable. -/
abbrev Ctx := List (String × Cat)

/-- The argument categories of a function symbol, read off its rule's non-terminal items in order. -/
def Rule.argSorts (r : Rule) : List Cat := r.items.flatMap Item.cats

mutual
  /-- `WellSorted p Γ t c`: term `t` has sort `c` in context `Γ`, with every subterm well-sorted. A
      variable has its context sort; an application has its function symbol's result sort, with arguments
      well-sorted at the symbol's argument sorts. -/
  inductive WellSorted (p : Presentation) (Γ : Ctx) : AST → Cat → Prop where
    | var {x : String} {c : Cat} : Γ.lookup x = some c → WellSorted p Γ (.var (.base x)) c
    | sexp {l : Label} {args : List AST} (r : Rule) :
        r ∈ p.terms → r.label = l → WellSortedList p Γ args r.argSorts →
        WellSorted p Γ (.sexp l args) r.cat
  /-- Pointwise well-sortedness of an argument list against a list of categories. -/
  inductive WellSortedList (p : Presentation) (Γ : Ctx) : List AST → List Cat → Prop where
    | nil : WellSortedList p Γ [] []
    | cons {a : AST} {c : Cat} {as : List AST} {cs : List Cat} :
        WellSorted p Γ a c → WellSortedList p Γ as cs → WellSortedList p Γ (a :: as) (c :: cs)
end

mutual
  /-- The substitution lemma (inst half): instantiating a well-sorted term with a substitution that is
      well-sorted for the source context yields a well-sorted term. Proved by mutual induction on the
      well-sortedness derivation: a variable is handled by the substitution hypothesis, an application
      recurses into its arguments. -/
  theorem inst_wellSorted {p : Presentation} {Γ Δ : Ctx} {bnds : List (String × AST)}
      (hb : ∀ x c, Δ.lookup x = some c → WellSorted p Γ (AST.inst bnds (.var (.base x))) c) :
      ∀ {t : AST} {c : Cat}, WellSorted p Δ t c → WellSorted p Γ (AST.inst bnds t) c
    | _, _, .var hx => hb _ _ hx
    | _, _, .sexp r hmem hlabel hargs => by
        have hargs' : WellSortedList p Γ (AST.instList bnds _) r.argSorts :=
          instList_wellSorted hb hargs
        exact WellSorted.sexp r hmem hlabel hargs'
  theorem instList_wellSorted {p : Presentation} {Γ Δ : Ctx} {bnds : List (String × AST)}
      (hb : ∀ x c, Δ.lookup x = some c → WellSorted p Γ (AST.inst bnds (.var (.base x))) c) :
      ∀ {ts : List AST} {cs : List Cat}, WellSortedList p Δ ts cs →
        WellSortedList p Γ (AST.instList bnds ts) cs
    | _, _, .nil => WellSortedList.nil
    | _, _, .cons ha has => WellSortedList.cons (inst_wellSorted hb ha) (instList_wellSorted hb has)
end


end MeTTaIL
