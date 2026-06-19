import MettaHyperonFull.Metagraph.Rewrite
import MettaHyperonFull.Reflection.SelfModification
import MettaHyperonFull.Operational.Trace

namespace Metta

/-- Codebases are represented as metagraph rewrite systems. This is a conservative encoding
    of the paper's ∞-groupoid / (∞,1)-topos discussion rather than a full HoTT library. -/
structure Codebase where
  rules : List MGRewrite
  programs : Space
  deriving Repr, Inhabited

/-- An execution-trace morphism maps trace indices to trace indices. -/
structure TraceMorphism where
  sourceLength : Nat
  targetLength : Nat
  mapIndex : Nat → Nat

/-- Approximate ∞-groupoid layer: objects are traces, morphisms are trace maps. -/
structure TraceGroupoidApprox where
  objects : List Trace
  morphisms : List TraceMorphism

/-- Ruliad node: a codebase rewriting another codebase. -/
structure RuliadNode where
  code : Codebase
  rewrites : List Codebase
  deriving Inhabited

end Metta
