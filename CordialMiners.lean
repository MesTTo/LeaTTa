/-
PoR-weighted Cordial Miners: a Lean 4 formalization of the leaderless DAG-based BFT consensus
protocol, following the blueprint "LLM + Lean Guided Synthesis and Verification of PoR-Weighted
Cordial Miners" (Goertzel). The next LeaTTa iteration, held to the LeaTTa bar (no `sorry`, `admit`,
`native_decide`, `partial`, or `unsafe`).

Layer order (later may import earlier, never the reverse):
  Foundation -> Spec -> Ref -> Trec -> Tfine -> CMIR -> Extract -> Sim -> Tests -> Proofs

What each layer holds:
  Foundation: weight and threshold arithmetic, the weighted-overlap lemma (FOUND-05), the prefix
    theory for output discipline (FOUND-08).
  Spec: the abstract protocol. Threshold finality and its self-enforcing safety (CERT-05/06), the
    blocklace and equivocation (BL-02/03/05/06), final-leader ratification (FL-07), the ordering
    contract and output consistency (TAU-04/08/09/10), and the dissemination and scheduler safety
    specs with their conditional liveness boundaries.
  Ref: executable references. The weighted certificate collector (CERT-02/03/04) and a verified
    concrete topological-sort ordering (deterministic, dup-free, topologically sorted, complete).
  Trec / Tfine: the coarse rewrite theory with causal well-formedness, and the fine evidence-carrying
    theory with the abstraction map and forward simulation that lifts coarse safety to it.
  CMIR / Extract: a MeTTa-IL atom IR and a lossless extraction (decode of encode is the original).
  Sim / Tests: an executable end-to-end protocol run, and kernel-checked worked examples.
  Proofs: the top-level safety aggregate (Theorem 4.54 core): Byzantine agreement, output
    consistency, and blocklace integrity, with leader-safety entering as an explicit hypothesis.
-/
import CordialMiners.Foundation.Basic
import CordialMiners.Foundation.FinsetWeight
import CordialMiners.Foundation.Prefix
import CordialMiners.Spec.Snapshot
import CordialMiners.Spec.WeightedCertificate
import CordialMiners.Spec.ThresholdFinality
import CordialMiners.Ref.WeightedCollector
import CordialMiners.Ref.TauOrder
import CordialMiners.Ref.AnchoredOrder
import CordialMiners.Ref.FinalizedAnchors
import CordialMiners.Spec.Blocklace
import CordialMiners.Spec.Equivocation
import CordialMiners.Spec.FinalLeader
import CordialMiners.Spec.TauOrderSpec
import CordialMiners.Spec.DisseminationSpec
import CordialMiners.Spec.SchedulerSpec
import CordialMiners.Trec.Syntax
import CordialMiners.Trec.Safety
import CordialMiners.Tfine.Abstraction
import CordialMiners.CMIR.Atom
import CordialMiners.Extract.MettaIL
import CordialMiners.Sim.Run
import CordialMiners.Proofs.EndToEndSafety
import CordialMiners.Tests.Examples
