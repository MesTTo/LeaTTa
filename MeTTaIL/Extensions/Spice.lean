/-
Module: MeTTaIL.Extensions.Spice
Layer: Extensions
Purpose: The spice rule (the "present moment") of Meredith's paper "How the Agents Got Their Present
  Moment". The paper modifies the rho-calculus COMM rule with bounded n-step lookahead, `Q --n--> {Q1,
  ..., Qm} ⟹ for(y <- x)P | x!(Q) → P{ @{Q1, ..., Qm} / y }`, where `Q --n--> S` is the set of terms
  reachable from Q in at most n reduction steps. The rule looks self-referential because the reduction
  used in `--n-->` includes COMM itself, and the paper asserts without proof that it is well-founded,
  grounding out via `Q --0--> {Q}`. Decomposed to its essence, the construction is bounded reachability
  over any one-step relation, defined by recursion on the fuel n. The file formalizes that core:
  `reachUpTo`, its grounding at n = 0, and the fact that it is a total, computable function, so the
  apparent circularity is resolved by construction. `reachUpTo` is structurally recursive on the fuel,
  so it computes. Mathlib-free.
Imports: none (Mathlib-free)
Trusted boundary: none
Main exports: stepN, reachUpTo, reachUpTo_zero, mem_frontier_stepN, self_mem_reachUpTo
Open obligations: the rho-calculus instance (taking `step` to be the one-step spice reduction, its COMM
  case consulting `reachUpTo` at strictly smaller fuel) is not formalized here.
-/

namespace MeTTaIL.Spice

/-- Bounded reachability: keep the current frontier and append one level of successors, recursing with
    one less fuel. The fuel `n` controls how many levels accumulate, so `stepN` at fuel `n` collects
    everything reachable in 0 to n steps, not just one level. Structural recursion on the fuel, so it
    computes; this is the well-founded core that the paper's modified COMM rule rests on. -/
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

/-- With fuel 0 the modified COMM rule sends the singleton `{Q}`, which grounds the recursion.
    Extracting `Q` from `{Q}` then recovers the original COMM rule, the grounding step the paper notes
    is needed; `@{Q}` is the code of the set, not the name `@Q`. The example restates the grounding
    `Q --0--> {Q}`. -/
example {α : Type} (step : α → List α) (q : α) :
    reachUpTo step 0 q = [q] := reachUpTo_zero step q

end MeTTaIL.Spice
