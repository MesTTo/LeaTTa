/-
Module: MeTTaIL
Layer: Library root
Purpose: The root of the MeTTaIL formalization in Lean 4, a faithful model of F1R3FLY-io's MeTTaIL
  (Meta Type Talk Intermediate Language), built alongside the LeaTTa MeTTa kernel. MeTTaIL is a
  meta-language: a `.module` is a program in an algebra of theory presentations, and the tool
  elaborates a chosen theory instance into a presentation (a graph-structured lambda theory) and can
  lift it from an untyped calculus to a typed one. The root aggregates the layers: the object syntax,
  the theory-instance algebra and presentation operations, the elaborator, the desugar/type-lift/
  monomorphize transforms, the GSLT reduction core and relation, the operational bridge, and the
  SKI and lambda calculus instances with the present-moment spice extension. The data model and
  passes are computable and Mathlib-free; the proofs live in a separate Mathlib-backed layer.
Imports: the MeTTaIL.Syntax, MeTTaIL.Theory, MeTTaIL.Transform, MeTTaIL.Semantics, MeTTaIL.Bridge,
  MeTTaIL.Calculi, and MeTTaIL.Extensions modules
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
-- Bridge: embedding LeaTTa's MeTTa terms into GSLT terms (faithful on the grounded-free fragment).
import MeTTaIL.Bridge.Operational
-- Layer 4: SKI combinatory logic instance with subject reduction (type soundness).
import MeTTaIL.Calculi.SKI
-- Layer 4: simply-typed lambda calculus (de Bruijn) with preservation and progress.
import MeTTaIL.Calculi.Lambda
-- Layer 4 (extension): the present-moment "spice" rule, bounded lookahead and its grounding.
import MeTTaIL.Extensions.Spice
