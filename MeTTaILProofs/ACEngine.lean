-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.ACEngine
Layer: Proofs
Purpose: Rewriting modulo AC, end to end. This wires the verified canonical form (MeTTaILProofs.AC) into
  the one-step engine (MeTTaIL.Semantics.Context) by the Maude strategy: to take a step modulo AC,
  canonicalise the term, take an ordinary base step, and recanonicalise. `RewStepModAC` is the standard
  rewrite relation modulo AC (the relation rewrites up to AC-equivalence on both sides). Two results make
  the strategy honest: `oneStepAC_respects` shows the engine is well-defined on AC-equivalence classes
  (AC-equivalent inputs give identical results, the coherence the canonical form buys us), and
  `oneStepAC_sound`/`evalAC_sound` show every step and every run is a genuine sequence of →_{R/AC} steps.
Imports: MeTTaIL.Semantics.Normal (hasRedex, oneStep_isSome_eq_hasRedex) which brings Context (RewStep,
  oneStep, oneStep_sound), MeTTaILProofs.AC (canon and its soundness/completeness), Mathlib.Logic.Relation
  (ReflTransGen)
Trusted boundary: none (fully proved)
Main exports: RewStepModAC, oneStepAC, oneStepAC_respects, oneStepAC_sound, evalAC, evalAC_sound,
  oneStepAC_isSome, CoherentAC, oneStepAC_complete
Open obligations: relational completeness in the presence of premised (conditional) rules is the
  conditional-rewrite work, inherited from the base engine (Normal); the AC completeness here is stated
  for base redexes (`hasRedex`) under the coherence condition `CoherentAC`.
-/
import MeTTaIL.Semantics.Normal
import MeTTaILProofs.AC
import Mathlib.Logic.Relation

namespace MeTTaIL.AC

open MeTTaIL

/-- Rewriting modulo AC, the standard relation →_{R/AC}: `t` rewrites to `t'` when `t` is AC-equivalent
    to some `u` that takes one base step to `u'`, with `u'` AC-equivalent to `t'`. -/
def RewStepModAC (acOp : Label → Bool) (p : Presentation) (t t' : AST) : Prop :=
  ∃ u u', ACEq acOp t u ∧ RewStep p u u' ∧ ACEq acOp u' t'

/-- One step of rewriting modulo AC: canonicalise, take a base step, recanonicalise. -/
def oneStepAC (acOp : Label → Bool) (p : Presentation) (t : AST) : Option AST :=
  (oneStep p (canon acOp t)).map (canon acOp)

/-- The engine is well-defined on AC-equivalence classes: AC-equivalent inputs give identical results.
    This is the coherence the canonical form provides, since `canon` is constant on each class. -/
theorem oneStepAC_respects (acOp : Label → Bool) {p : Presentation} {t t2 : AST}
    (h : ACEq acOp t t2) : oneStepAC acOp p t = oneStepAC acOp p t2 := by
  unfold oneStepAC; rw [canon_complete acOp h]

/-- Soundness: every step the modulo-AC engine takes is a genuine →_{R/AC} step. The input is
    AC-equivalent to its canonical form, the base engine takes a real `RewStep` there, and the output is
    the recanonicalised reduct, AC-equivalent to that reduct. -/
theorem oneStepAC_sound (acOp : Label → Bool) {p : Presentation} {t t' : AST}
    (h : oneStepAC acOp p t = some t') : RewStepModAC acOp p t t' := by
  unfold oneStepAC at h
  rcases hs : oneStep p (canon acOp t) with _ | s
  · rw [hs] at h; simp at h
  · rw [hs, Option.map_some] at h
    injection h with h
    subst h
    exact ⟨canon acOp t, s, (canon_sound acOp t).symm, oneStep_sound p (canon acOp t) hs,
      (canon_sound acOp s).symm⟩

/-- Fuel-bounded normalization modulo AC: iterate the modulo-AC step. -/
def evalAC (acOp : Label → Bool) (p : Presentation) : Nat → AST → AST
  | 0, t => t
  | n + 1, t =>
      match oneStepAC acOp p t with
      | some t' => evalAC acOp p n t'
      | none => t

/-- Soundness of the modulo-AC normalizer: its result is reachable from the input by →_{R/AC} steps. -/
theorem evalAC_sound (acOp : Label → Bool) (p : Presentation) (fuel : Nat) (t : AST) :
    Relation.ReflTransGen (RewStepModAC acOp p) t (evalAC acOp p fuel t) := by
  induction fuel generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      cases hs : oneStepAC acOp p t with
      | none =>
          rw [show evalAC acOp p (n + 1) t = t from by simp [evalAC, hs]]
      | some t' =>
          rw [show evalAC acOp p (n + 1) t = evalAC acOp p n t' from by simp [evalAC, hs]]
          exact (Relation.ReflTransGen.single (oneStepAC_sound acOp hs)).trans (ih t')

/-- A term is normal modulo AC for this engine when no modulo-AC step applies, equivalently when its
    canonical form is a base normal form. -/
def IsNormalModAC (acOp : Label → Bool) (p : Presentation) (t : AST) : Prop :=
  oneStepAC acOp p t = none

/-! ## Completeness: when the engine acts, and coherence

The engine takes a step exactly when the canonical form has a base redex. Whether that captures every
`→_{R/AC}` step is the coherence question: the canonical form must not lose a redex that some other
AC-representative has. `CoherentAC` names that condition, and under it the engine is complete. -/

/-- The engine takes a step exactly when the canonical form has a base redex. No coherence assumption is
    needed for this characterization; it follows from base-engine completeness on the canonical form. -/
theorem oneStepAC_isSome (acOp : Label → Bool) (p : Presentation) (t : AST) :
    (oneStepAC acOp p t).isSome = hasRedex p (canon acOp t) := by
  simp only [oneStepAC, Option.isSome_map, oneStep_isSome_eq_hasRedex]

/-- Being normal modulo AC means the canonical form has no base redex anywhere. -/
theorem isNormalModAC_iff_hasRedex (acOp : Label → Bool) (p : Presentation) (t : AST) :
    IsNormalModAC acOp p t ↔ hasRedex p (canon acOp t) = false := by
  unfold IsNormalModAC
  rw [← oneStepAC_isSome]
  simp [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

/-- Every base redex gives a genuine context rewrite (the easy half of the engine/relation bridge). -/
theorem exists_rewStep_of_hasRedex {p : Presentation} {u : AST} (hu : hasRedex p u = true) :
    ∃ u', RewStep p u u' := by
  have hsome : (oneStep p u).isSome = true := by rw [oneStep_isSome_eq_hasRedex]; exact hu
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨u', oneStep_sound p u hu'⟩

/-- Coherence of a presentation with AC: canonicalising never loses a redex that some AC-equivalent term
    has. This is the condition (Maude's coherence) under which the canonical-form strategy is complete:
    it makes the canonical form a redex-maximal representative of its AC-equivalence class. It is an
    assumed side-condition, not established here for arbitrary presentations (a syntactic criterion
    guaranteeing it is future work); `coherentAC_of_no_rewrites` shows it is at least satisfiable, so the
    completeness result below is conditional but not vacuous. -/
def CoherentAC (acOp : Label → Bool) (p : Presentation) : Prop :=
  ∀ t u, ACEq acOp t u → hasRedex p u = true → hasRedex p (canon acOp t) = true

/-- Completeness under the assumed coherence side-condition `CoherentAC`: if any AC-representative of `t`
    has a redex, the modulo-AC engine takes a step. With `exists_rewStep_of_hasRedex` this says the engine
    never stalls while some AC-equivalent term can still be rewritten. The result is conditional on
    coherence, which is assumed rather than proven in general (see `CoherentAC`). -/
theorem oneStepAC_complete (acOp : Label → Bool) {p : Presentation} (hco : CoherentAC acOp p)
    {t u : AST} (htu : ACEq acOp t u) (hu : hasRedex p u = true) :
    (oneStepAC acOp p t).isSome = true := by
  rw [oneStepAC_isSome]; exact hco t u htu hu

mutual
  /-- With no rewrite rules, no term has a redex anywhere. -/
  theorem hasRedex_false_of_no_rewrites {p : Presentation} (hp : p.rewrites = []) :
      ∀ t, hasRedex p t = false
    | .var _ => by simp [hasRedex, baseReducts, hp]
    | .sexp _ args => by
        simp [hasRedex, baseReducts, hp, hasRedexList_false_of_no_rewrites hp args]
    | .subst b r _ => by
        simp [hasRedex, baseReducts, hp, hasRedex_false_of_no_rewrites hp b,
          hasRedex_false_of_no_rewrites hp r]
  theorem hasRedexList_false_of_no_rewrites {p : Presentation} (hp : p.rewrites = []) :
      ∀ ts, hasRedexList p ts = false
    | [] => by simp [hasRedexList]
    | a :: as => by
        simp [hasRedexList, hasRedex_false_of_no_rewrites hp a,
          hasRedexList_false_of_no_rewrites hp as]
end

/-- Coherence is satisfiable: a presentation with no rewrite rules is coherent, vacuously, since nothing
    is reducible. So `CoherentAC` is a consistent side-condition rather than an empty one, and
    `oneStepAC_complete` is a real (if conditional) completeness statement. -/
theorem coherentAC_of_no_rewrites (acOp : Label → Bool) {p : Presentation} (hp : p.rewrites = []) :
    CoherentAC acOp p := by
  intro _ u _ hu
  simp [hasRedex_false_of_no_rewrites hp u] at hu

end MeTTaIL.AC
