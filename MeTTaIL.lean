-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaIL
Layer: Library root
Purpose: The root of the MeTTaIL formalization in Lean 4, a faithful model of F1R3FLY-io's MeTTaIL
  (Meta Type Talk Intermediate Language), built alongside the LeaTTa MeTTa kernel. MeTTaIL is a
  meta-language: a `.module` is a program in an algebra of theory presentations, and the tool
  elaborates a chosen theory instance into a presentation (a graph-structured lambda theory) and can
  lift it from an untyped calculus to a typed one. The root aggregates the layers: the object syntax,
  the theory-instance algebra and presentation operations, the elaborator, the desugar/type-lift/
  monomorphize transforms, the GSLT reduction core and relation, the executable runtime (the one-step
  reducer, the fuel-bounded normalizer, and the S-expression front end), the denotational-semantics
  interface for full abstraction, the operational bridge, and the SKI and lambda calculus instances
  with the present-moment spice extension. The data model and passes are computable and Mathlib-free;
  the proofs live in a separate Mathlib-backed layer.
Imports: the MeTTaIL.Syntax, MeTTaIL.Theory, MeTTaIL.Transform, MeTTaIL.Semantics, MeTTaIL.Runtime,
  MeTTaIL.Bridge, MeTTaIL.Calculi, and MeTTaIL.Extensions modules
Trusted boundary: none
Main exports: (aggregator; re-exports the library)
Open obligations: none
-/

-- Layer 1: the object syntax of presentations.
import MeTTaIL.Syntax
-- Layer 1: the theory-instance algebra elaborated to presentations.
import MeTTaIL.Theory.Instance
-- Layer 1: pure presentation operations (union, intersection, difference, accessors).
import MeTTaIL.Theory.Ops
-- Layer 1: category renaming and constructor relabeling (addExports rename, addReplacements).
import MeTTaIL.Theory.Rename
-- Layer 1: the elaboration interpreter.
import MeTTaIL.Theory.Elaborate
-- Layer 2: the DesugarBinds transformation pass.
import MeTTaIL.Transform.Desugar
-- Layer 2: the Hypercube type-lift pass.
import MeTTaIL.Transform.TypeLift
-- Layer 2: the BNFCRenderer monomorphization pass.
import MeTTaIL.Transform.Monomorphize
-- Layer 3: the GSLT reduction core (matching, substitution, rewrite application).
import MeTTaIL.Semantics.Reduce
-- Layer 3: the GSLT reduction relation (base + premised/congruence rules) + matcher soundness.
import MeTTaIL.Semantics.Relation
-- Runtime: the executable one-step reducer over the relation (leftmost-outermost), its fuel-bounded
-- normalizer, the normal-form characterization, and conditional termination under a measure.
import MeTTaIL.Semantics.Context
import MeTTaIL.Semantics.Eval
import MeTTaIL.Semantics.Normal
import MeTTaIL.Semantics.Terminate
-- Runtime: evaluation-context strategies (K-style strictness) restricting where the reducer descends.
import MeTTaIL.Semantics.Strategy
-- Runtime: the sort discipline derived from the grammar, with subject reduction (the runtime keeps a
-- term at its sort).
import MeTTaIL.Semantics.Sorts
-- Runtime: a recursive all-subterms sort system with its substitution lemma (deeper than head-sort).
import MeTTaIL.Semantics.WellSorted
-- Runtime: operational semantics in logical form (Stay-Meredith), the spatial-behavioral logic derived
-- from a presentation, with the arrow type as a special case of the possibly modal operator.
import MeTTaIL.Semantics.OSLF
-- Runtime: the denotational-semantics interface for context-labelled systems and full abstraction.
import MeTTaIL.Semantics.Denotational
-- Runtime: abstract cost round trips, starvation deadlock, and wrapped trace preservation.
import MeTTaIL.Semantics.CostRoundTrip
-- Runtime: native-carrier obligations for interpreted types inside MeTTaIL presentations.
import MeTTaIL.Semantics.Native
-- Runtime: surface-language invariance for concrete readings over native carriers.
import MeTTaIL.Semantics.NativeGrammar
-- Runtime: OSLF native types as sort-predicate pairs over presentations.
import MeTTaIL.Semantics.NativeTypes
-- Runtime: finite sort-assignment centers for generated modal and spatial hypercubes.
import MeTTaIL.Semantics.Hypercube
-- Runtime: the red/black reflective-universe and final-coalgebra interfaces.
import MeTTaIL.Semantics.KnottedUniverse
-- Runtime: the finitary rset core with red sets whose atoms are black sets, and conversely.
import MeTTaIL.Semantics.RSet
-- Runtime: interacting trie maps and the reflective RITM equation used by the denotational target.
import MeTTaIL.Semantics.InteractingTrieMap
-- Runtime: a small rho-calculus target plus the one-channel RSpace COMM boundary used by the compiler
-- correspondence work.
import MeTTaIL.Semantics.Rho
-- Runtime: K-shaped rho cells and the persistent-receive step reified to rho COMM.
import MeTTaIL.Semantics.RhoKMachine
-- Runtime: packet-level bridge from the existing base matcher to a rho listener emission.
import MeTTaIL.Semantics.RhoCompiler
-- Runtime: a generic S-expression front end (parse and pretty-print) and the `run` entry point.
import MeTTaIL.Runtime.Sexpr
import MeTTaIL.Runtime.Generic
-- Runtime: external file surface for runnable dialect presentations.
import MeTTaIL.Runtime.LanguageFile
-- Bridge: embedding LeaTTa's MeTTa terms into GSLT terms (faithful on the grounded-free fragment).
import MeTTaIL.Bridge.Operational
-- Layer 4: SKI combinatory logic instance with subject reduction (type soundness).
import MeTTaIL.Calculi.SKI
-- Layer 4: simply-typed lambda calculus (de Bruijn) with preservation and progress.
import MeTTaIL.Calculi.Lambda
-- Layer 4 (extension): the present-moment "spice" rule, bounded lookahead and its grounding.
import MeTTaIL.Extensions.Spice
