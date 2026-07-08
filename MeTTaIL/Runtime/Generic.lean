-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL.Runtime.Generic
Layer: Runtime
Purpose: The end-to-end runtime entry point. `run` parses a term string, normalizes it with the verified
  `eval`, and prints the result, so a dialect's presentation plus a term string yields an answer string.
  This is the "tweak the LanguageDef, get a runtime" surface, and the reduction it performs is sound by
  `eval_sound`: the printed term is reachable from the input by the presentation's own rewrites.
Imports: MeTTaIL.Semantics.Eval, MeTTaIL.Runtime.Sexpr, MeTTaIL.Theory.Elaborate,
  MeTTaIL.Transform.Monomorphize
Trusted boundary: none
Main exports: run, run_sound, runInst, runInst_ok, run_monomorphize, runInstMono, runInstMono_eq_runInst
Open obligations: none for the compile path; `runInstMono` adds the monomorphize pass and is proved
  behavior-preserving.
-/
import MeTTaIL.Semantics.Eval
import MeTTaIL.Runtime.Sexpr
import MeTTaIL.Theory.Elaborate
import MeTTaIL.Transform.Monomorphize

namespace MeTTaIL

/-- Parse a term string, normalize it with the verified reducer, and print the result. Returns `none`
    only if the input does not parse. The reduction is sound by `eval_sound`. -/
def run (p : Presentation) (fuel : Nat) (s : String) : Option String :=
  (parse s).map (fun t => pretty (eval p fuel t))

/-- Soundness of the entry point at the string level: when `run` prints an answer, the input parses to a
    term `t`, and the printed answer is some `t'` that `t` actually reaches by the presentation's rewrites
    (`RewStepMany`). Makes the prose guarantee a checked theorem; the reduction part is `eval_sound`. -/
theorem run_sound {p : Presentation} {fuel : Nat} {s : String} {out : String}
    (h : run p fuel s = some out) :
    ∃ t t', parse s = some t ∧ RewStepMany p t t' ∧ pretty t' = out := by
  unfold run at h
  cases hp : parse s with
  | none => rw [hp] at h; simp at h
  | some t =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨t, eval p fuel t, rfl, eval_sound p fuel t, h⟩

/-- The full compile path: elaborate a theory instance (a `.module`-style program in the presentation
    algebra) to a `Presentation`, then run a term string through the verified normalizer. This is the
    "tweak the LanguageDef, get a runtime" pipeline end to end: change the theory instance and the
    runtime follows. Returns the elaboration error, or the run result (`none` if the term does not
    parse). -/
def runInst (ctx : ElabCtx) (ti : TheoryInst) (fuel : Nat) (s : String) :
    Except String (Option String) :=
  (elaborate ctx ti).map (fun p => run p fuel s)

/-- `runInst` is exactly elaborate-then-run: a successful result comes from running the elaborated
    presentation, so it inherits `run`'s guarantee (the printed term is reachable from the input by the
    elaborated presentation's own rewrites, via `eval_sound`). -/
theorem runInst_ok {ctx : ElabCtx} {ti : TheoryInst} {fuel : Nat} {s : String} {r : Option String}
    (h : runInst ctx ti fuel s = .ok r) :
    ∃ p, elaborate ctx ti = .ok p ∧ run p fuel s = r := by
  unfold runInst at h
  cases he : elaborate ctx ti with
  | error e => simp [he, Except.map] at h
  | ok p => simp only [he, Except.map, Except.ok.injEq] at h; exact ⟨p, rfl, h⟩

/-! ## Monomorphization is behavior-preserving for the runtime

The documented pipeline is `.module -> elaborate -> monomorphize -> run`. The monomorphize pass rewrites
the grammar (it replaces higher-order sorts) but carries the rewrites through unchanged, and the reducer
reads a presentation only through its rewrites. So adding the pass does not change what the runtime
computes; `runInstMono` is proved equal to `runInst`. -/

mutual
  /-- The one-step reducer depends on a presentation only through its rewrites. -/
  theorem oneStep_eq_of_rw {p p' : Presentation} (hrw : p.rewrites = p'.rewrites) :
      ∀ t, oneStep p t = oneStep p' t
    | .var _ => by simp only [oneStep, baseReducts, hrw]
    | .sexp _ args => by simp only [oneStep, baseReducts, hrw, oneStepList_eq_of_rw hrw args]
    | .subst b r _ => by
        simp only [oneStep, baseReducts, hrw, oneStep_eq_of_rw hrw b, oneStep_eq_of_rw hrw r]
  /-- The list reducer depends on a presentation only through its rewrites. -/
  theorem oneStepList_eq_of_rw {p p' : Presentation} (hrw : p.rewrites = p'.rewrites) :
      ∀ args, oneStepList p args = oneStepList p' args
    | [] => by simp only [oneStepList]
    | a :: as => by simp only [oneStepList, oneStep_eq_of_rw hrw a, oneStepList_eq_of_rw hrw as]
end

/-- The normalizer depends on a presentation only through its rewrites. -/
theorem eval_eq_of_rw {p p' : Presentation} (hrw : p.rewrites = p'.rewrites) :
    ∀ (fuel : Nat) (t : AST), eval p fuel t = eval p' fuel t
  | 0, _ => rfl
  | n + 1, t => by
      simp only [eval, oneStep_eq_of_rw hrw t]
      cases oneStep p' t with
      | none => rfl
      | some t' => exact eval_eq_of_rw hrw n t'

/-- `run` depends on a presentation only through its rewrites. -/
theorem run_eq_of_rw {p p' : Presentation} (hrw : p.rewrites = p'.rewrites) (fuel : Nat) (s : String) :
    run p fuel s = run p' fuel s := by
  simp only [run, eval_eq_of_rw hrw fuel]

/-- Monomorphization does not change the runtime behavior: it carries the rewrites through unchanged. -/
theorem run_monomorphize (p : Presentation) (fuel : Nat) (s : String) :
    run (monomorphize p) fuel s = run p fuel s :=
  run_eq_of_rw (p := monomorphize p) (p' := p) rfl fuel s

/-- The full compile path with monomorphization: elaborate a theory instance, monomorphize the grammar,
    then run a term string. -/
def runInstMono (ctx : ElabCtx) (ti : TheoryInst) (fuel : Nat) (s : String) :
    Except String (Option String) :=
  (elaborate ctx ti).map (fun p => run (monomorphize p) fuel s)

/-- The monomorphize pass is behavior-preserving end to end: `runInstMono` agrees with `runInst`. -/
theorem runInstMono_eq_runInst (ctx : ElabCtx) (ti : TheoryInst) (fuel : Nat) (s : String) :
    runInstMono ctx ti fuel s = runInst ctx ti fuel s := by
  unfold runInstMono runInst
  simp only [run_monomorphize]

end MeTTaIL
