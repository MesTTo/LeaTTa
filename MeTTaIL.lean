/-
MeTTaIL in Lean 4: a faithful formalization of F1R3FLY-io's MeTTaIL (Meta Type Talk Intermediate
Language), built alongside the LeaTTa MeTTa kernel, operational semantics, and metatheory.

MeTTaIL is a meta-language: a `.module` is a program in an algebra of theory presentations, and the
tool elaborates a chosen theory instance into a presentation (a graph-structured lambda theory) and
can lift it from an untyped calculus to a typed one. See `MeTTaIL/SPECIFICATION.md` for the plan.

This library follows LeaTTa's computability split: the data model, elaboration, transformations, and
reduction are computable and Mathlib-free; the proofs about them live in a Mathlib-backed layer.
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
