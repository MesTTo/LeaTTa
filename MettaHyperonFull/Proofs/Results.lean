/-
Module: MettaHyperonFull.Proofs.Results
Layer: Proofs
Purpose: The abstract machine is deterministic. interpretStack1, interpretFuel, and mettaEval are
  total functions of their inputs, so every configuration has a unique successor and a unique result.
  MeTTa's nondeterminism is reified in the returned list, not left as don't-know nondeterminism in
  the transition relation, which is the replayable discipline a blockchain VM needs. Also records the
  driver's base cases, accumulator correctness, and the cartesian branching-factor law.
Imports: MettaHyperonFull.Proofs.Basic
Trusted boundary: none (fully proved)
Main exports: interpretStack1_deterministic, interpretFuel_deterministic, mettaEval_deterministic,
  interpretFuel_nil, interpretFuel_zero_cons, interpretFuel_done, cartesian_cons, cartesian_length
Open obligations: none
-/
import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: the abstract machine is deterministic

For use as an on-chain / smart-contract language, MeTTa execution must be **predictable**: the
same program in the same state must always produce the same outcome.

The minimal interpreter is a *deterministic* abstract machine. One step,
`interpretStack1 : MinEnv → Nat → St → Item → List Item × St`, and the driver
`interpretFuel : … → List (Atom × Bindings) × St` are **total functions** of their inputs, so
every configuration has a unique successor and a unique result. MeTTa's nondeterminism (a query
may yield several results) is *reified in the returned `List`*: it is data the function computes,
not "don't-know" nondeterminism in the transition relation. That is the discipline a
blockchain VM needs: replayable, with all branching observable in the output rather than hidden in
evaluation order.

The module records that determinism explicitly, the definitional base cases of the driver, and
the law governing `cartesian`, the helper that forms the product of the (nondeterministic)
argument-evaluation results in `mettaEval`.
-/

namespace Metta
open Metta.Minimal

/-- **Determinism of one step.** `interpretStack1` is a function, so a configuration steps to a
unique successor multiset-of-items and a unique threaded state, so the transition relation it
induces is single-valued. -/
theorem interpretStack1_deterministic {env : MinEnv} {fuel : Nat} {st : St} {it : Item}
    {r₁ r₂ : List Item × St} (h₁ : interpretStack1 env fuel st it = r₁)
    (h₂ : interpretStack1 env fuel st it = r₂) : r₁ = r₂ :=
  h₁.symm.trans h₂

/-- **Determinism of the driver.** `interpretFuel` is a function: a program run to a fuel bound
yields a unique result list and final state. -/
theorem interpretFuel_deterministic {env : MinEnv} {fuel : Nat} {st : St} {work : List Item}
    {done : List (Atom × Bindings)} {r₁ r₂ : List (Atom × Bindings) × St}
    (h₁ : interpretFuel env fuel st work done = r₁)
    (h₂ : interpretFuel env fuel st work done = r₂) : r₁ = r₂ :=
  h₁.symm.trans h₂

/-- **Determinism of full evaluation.** `mettaEval` is a function of its inputs. -/
theorem mettaEval_deterministic {env : MinEnv} {fuel : Nat} {st : St} {bnd : Bindings} {a : Atom}
    {r₁ r₂ : List (Atom × Bindings) × St} (h₁ : mettaEval env fuel st bnd a = r₁)
    (h₂ : mettaEval env fuel st bnd a = r₂) : r₁ = r₂ :=
  h₁.symm.trans h₂

/-- With no work left, the driver returns the accumulated results (un-reversed) and the unchanged
state, at any fuel. -/
theorem interpretFuel_nil (env : MinEnv) (fuel : Nat) (st : St)
    (done : List (Atom × Bindings)) : interpretFuel env fuel st [] done = (done.reverse, st) := by
  cases fuel <;> simp [interpretFuel]

/-- When fuel is exhausted with work remaining, the driver harvests *every* item: already-final
items yield their result, and each unfinished item yields a `StackOverflow` error (`exhaustedPair`), so
exhaustion is reported, never silently truncated. -/
theorem interpretFuel_zero_cons (env : MinEnv) (st : St) (it : Item) (rest : List Item)
    (done : List (Atom × Bindings)) :
    interpretFuel env 0 st (it :: rest) done
      = (done.reverse ++ (it :: rest).map (fun i => if isFinal i then finalPair i else exhaustedPair i), st) := by
  simp [interpretFuel]

/-- **Accumulator correctness.** The `done` accumulator threaded through the driver is exactly a
reversed prefix of the output: `interpretFuel … work done` equals
`done.reverse ++ (interpretFuel … work []).1` with the same final state. So the accumulator never
changes *which* results are produced: it is a faithful accumulator, which is what lets us reason
about the driver as if it simply returned its results. (Induction on `fuel`; the inductive step
rewrites both occurrences of the recursive call by the inductive hypothesis and reconciles the
`reverse`/`append` bookkeeping.) -/
theorem interpretFuel_done (env : MinEnv) (fuel : Nat) :
    ∀ (st : St) (work : List Item) (done : List (Atom × Bindings)),
      interpretFuel env fuel st work done
        = (done.reverse ++ (interpretFuel env fuel st work []).1,
           (interpretFuel env fuel st work []).2) := by
  induction fuel with
  | zero =>
      intro st work done
      cases work with
      | nil => simp [interpretFuel]
      | cons it rest => simp [interpretFuel]
  | succ f ih =>
      intro st work done
      cases work with
      | nil => simp [interpretFuel]
      | cons it rest =>
          cases h : interpretStack1 env f st it with
          | mk results st' =>
              simp only [interpretFuel, h, List.append_nil]
              -- name the two head-bucketed sublists so the IH applies by name
              generalize List.filter (fun r => !isFinal r) results ++ rest = W
              generalize List.map finalPair (List.filter isFinal results) = F
              rw [ih st' W (F.reverse ++ done), ih st' W F.reverse]
              simp [List.reverse_append, List.append_assoc]

theorem cartesian_nil {α : Type} : cartesian ([] : List (List α)) = [[]] := rfl

/-- Unfolding law: `cartesian` prepends each element of the head list to each tuple of the product
of the tail. -/
theorem cartesian_cons {α : Type} (xs : List α) (rest : List (List α)) :
    cartesian (xs :: rest) = xs.flatMap (fun x => (cartesian rest).map (fun t => x :: t)) := rfl

/-- **Size of the nondeterministic product.** The number of combined results is the product of the
per-argument result counts, so the branching factor of an evaluation is the product of
the branching factors of its arguments. -/
theorem cartesian_length {α : Type} (xss : List (List α)) :
    (cartesian xss).length = (xss.map List.length).prod := by
  induction xss with
  | nil => simp [cartesian]
  | cons xs rest ih =>
      simp only [cartesian, List.length_flatMap, List.length_map, ih, List.map_cons,
        List.prod_cons, List.map_const', List.sum_replicate, smul_eq_mul]

end Metta
