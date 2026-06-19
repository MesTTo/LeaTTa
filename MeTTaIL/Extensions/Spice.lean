/-
The spice rule (the "present moment") of Meredith's paper "How the Agents Got Their Present Moment".

The paper modifies the rho-calculus COMM rule with bounded n-step lookahead:

  Q --n--> {Q1, ..., Qm}  ⟹  for(y <- x)P | x!(Q)  →  P{ @{Q1, ..., Qm} / y }

where `Q --n--> S` is the set of terms reachable from Q in at most n reduction steps. The rule looks
self-referential, because the reduction used in `--n-->` includes COMM itself. The paper asserts,
without proof, that this is well-founded, grounding out via `Q --0--> {Q}`.

Decomposed to its essence, the construction is bounded reachability over any one-step relation,
defined by recursion on the fuel n. This file formalizes that core: `reachUpTo`, its grounding at
n = 0, and the fact that it is a total, computable function (so the apparent circularity is resolved
by construction). The rho-calculus instance takes `step` to be the one-step spice reduction, whose
COMM case consults `reachUpTo` at strictly smaller fuel, so the same fuel structure makes the mutual
definition well-founded.

`reachUpTo` is structurally recursive on the fuel, so it computes (the example below is by `decide`).
This layer is Mathlib-free.
-/

namespace MeTTaIL.Spice

/-- One breadth-first level of lookahead: keep the current frontier, then recurse on its successors
    with one less fuel. Structural recursion on the fuel `n`, so it computes; this is the well-founded
    core that the paper's modified COMM rule rests on. -/
def stepN {α : Type} (step : α → List α) : Nat → List α → List α
  | 0, frontier => frontier
  | n + 1, frontier => frontier ++ stepN step n (frontier.flatMap step)

/-- The at-most-n-step reachable list of a term: the present-moment paper's `Q --n--> {...}`. -/
def reachUpTo {α : Type} (step : α → List α) (n : Nat) (q : α) : List α := stepN step n [q]

/-- Grounding: zero-step lookahead reaches exactly the starting term, i.e. `Q --0--> {Q}`. This is
    the base case that makes the apparently self-referential modified COMM rule well-founded. -/
theorem reachUpTo_zero {α : Type} (step : α → List α) (q : α) :
    reachUpTo step 0 q = [q] := rfl

/-- The current frontier is always contained in its bounded reachable set, at any fuel. -/
theorem mem_frontier_stepN {α : Type} (step : α → List α) :
    ∀ (n : Nat) (frontier : List α) {x : α}, x ∈ frontier → x ∈ stepN step n frontier
  | 0, _, _, h => h
  | n + 1, frontier, _, h =>
      List.mem_append_left (stepN step n (frontier.flatMap step)) h

/-- The starting term is always within its own bounded reachable set, at any fuel. -/
theorem self_mem_reachUpTo {α : Type} (step : α → List α) (n : Nat) (q : α) :
    q ∈ reachUpTo step n q :=
  mem_frontier_stepN step n [q] (List.mem_singleton.mpr rfl)

/-- A concrete lookahead: counting down from 3 with a single successor each step. At fuel 2 the
    reachable list is `[3, 2, 1]`. The definition computes, so this is checked by `decide`. -/
example :
    (reachUpTo (fun k => if k = 0 then [] else [k - 1]) 2 3 == [3, 2, 1]) = true := by decide

/-- With fuel 0 the modified COMM rule sends the singleton `{Q}`, i.e. just `Q`, recovering the
    ordinary rho-calculus COMM rule. -/
example {α : Type} (step : α → List α) (q : α) :
    reachUpTo step 0 q = [q] := reachUpTo_zero step q

end MeTTaIL.Spice
