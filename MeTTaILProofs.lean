/-
Module: MeTTaILProofs
Layer: Library root
Purpose: The root of the Mathlib-backed metatheory of MeTTaIL. It aggregates decidable equality of
  the data model, the mq-calculus probability results, the elaboration and transformation pipeline
  invariants, the presentation lattice laws, Church-Rosser confluence for SKI combinatory logic and
  for beta reduction of the lambda calculus, and the runtime metatheory: confluence of the one-step
  engine (Newman), a verified total order on terms, and rewriting modulo AC (a canonical form and the
  engine built on it).
Imports: the MeTTaILProofs modules (DecEq, MQCalculus, Pipeline, Lattice, SKIConfluence,
  LambdaConfluence, Newman, Order, AC, ACEngine)
Trusted boundary: none
Main exports: (aggregator; re-exports the library)
Open obligations: none
-/
-- Decidable equality and LawfulBEq for the whole data model.
import MeTTaILProofs.DecEq
-- The mq-calculus (communication = measurement): Born-rule probability conservation.
import MeTTaILProofs.MQCalculus
-- Elaboration / transformation pipeline invariants.
import MeTTaILProofs.Pipeline
-- The presentation lattice laws (union / intersection / difference as set operations).
import MeTTaILProofs.Lattice
-- Church-Rosser / confluence for SKI combinatory logic.
import MeTTaILProofs.SKIConfluence
-- Church-Rosser / confluence of beta reduction for the lambda calculus.
import MeTTaILProofs.LambdaConfluence
-- Runtime metatheory: confluence of the one-step engine (Newman's lemma, unique normal forms).
import MeTTaILProofs.Newman
-- Runtime metatheory: disjoint-redex local confluence (Huet Critical Pair Theorem, Case 1).
import MeTTaILProofs.LocalConfluence
-- Runtime metatheory: the Parallel Moves Lemma (disjoint case of the Critical Pair Theorem) over a
-- first-order term model with positions.
import MeTTaILProofs.CriticalPairs
-- Confluence of the premised (conditional) rewrite fragment: the stratified oriented conditional rewrite
-- relation, the conditional Parallel Moves Lemma, and the conditional Critical Pair Theorem (soundness).
import MeTTaILProofs.ConditionalCP
-- Runtime metatheory: connecting the first-order Critical Pair Theorem to the runtime AST/RewStep via a
-- faithful embedding (work toward removing the clean-model compromise).
import MeTTaILProofs.CPRuntime
-- Runtime metatheory: premised `sexp` argument congruence rules are conservative over the embedded base
-- runtime relation, so the CPRuntime confluence transport also covers those conditional rules.
import MeTTaILProofs.ConditionalCPRuntime
-- First-order unification over FOTerm (toward an effective critical-pair check, compromise #3).
import MeTTaILProofs.Unify
-- Stability of rewriting under substitution, toward the effective critical-pair check (compromise #3).
import MeTTaILProofs.CPDecide
-- Non-vacuity witnesses: unify computes, and CPJ_of_check is usable end-to-end.
import MeTTaILProofs.CPDemo
-- Runtime metatheory: the verified total order on terms (foundation for canonical-form AC).
import MeTTaILProofs.Order
-- Runtime metatheory: rewriting modulo AC via a canonical form (sound, complete, decidable).
import MeTTaILProofs.AC
-- Runtime metatheory: the canonical form wired into the one-step engine (rewriting modulo AC).
import MeTTaILProofs.ACEngine
-- Runtime metatheory: executable AC-aware matching for the linear collection fragment.
import MeTTaILProofs.ACMatch
-- Runtime metatheory: normalization modulo AC and its coherence (Church-Rosser modulo AC).
import MeTTaILProofs.ACNormal
-- Runtime metatheory: commutative variadic (n-ary) AC operators.
import MeTTaILProofs.ACVariadic
-- Runtime metatheory: full associative-commutative variadic (n-ary) AC operators.
import MeTTaILProofs.ACVariadicFull
-- Runtime metatheory: discharging the head-sort preservation side-condition (matcher head-inversion,
-- a checkable per-rule criterion, and a worked presentation).
import MeTTaILProofs.SortSoundness
-- Runtime metatheory: the matching half of the substitution lemma and full subject reduction for the
-- recursive (all-subterms) sort system.
import MeTTaILProofs.SubjectReduction
-- Runtime metatheory: matcher correctness (a successful match reconstructs the term, so a base step is a
-- genuine rule application), modeled on MORK's Verus BindingEnv/VarRefRecheck proofs.
import MeTTaILProofs.MatcherCorrect
-- Runtime metatheory: the greatest-fixed-point OSLF modalities (coinductive confinement/safety).
import MeTTaILProofs.OSLFRec
-- Runtime metatheory: the categorical structure of OSLF (dia a closure-operator monad, box an interior
-- comonad, spatial a bifunctor), the concrete content of "logic as a distributive law".
import MeTTaILProofs.OSLFCat
-- Beck's theorem in the general (non-thin) 2-category Cat: a distributive law of two CategoryTheory.Monads
-- yields a composite monad. The general version of OSLFCat's thin/poset composeClosure.
import MeTTaILProofs.DistributiveLaw
-- Build-visible axiom audit for the headline theorem surfaces.
import MeTTaILProofs.AxiomAudit
