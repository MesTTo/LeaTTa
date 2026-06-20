/-
PoR-weighted Cordial Miners: a Lean 4 formalization of the leaderless DAG-based BFT consensus
protocol, following the blueprint "LLM + Lean Guided Synthesis and Verification of PoR-Weighted
Cordial Miners" (Goertzel). This is the next LeaTTa iteration; it is a work in progress, built
milestone by milestone (Experiment 0 onward) and held to the LeaTTa bar (no `sorry`, `admit`,
`native_decide`, `partial`, or `unsafe`).

Layer order (later may import earlier, never the reverse):
  Foundation -> Spec -> Ref -> Trec -> Tfine -> CMIR -> Extract -> Sim -> Tests -> Proofs

Experiment 0 (foundation): the weight and threshold arithmetic, including the weighted-overlap lemma
that underpins threshold-finality safety.
-/
import CordialMiners.Foundation.Basic
import CordialMiners.Foundation.FinsetWeight
import CordialMiners.Foundation.Prefix
import CordialMiners.Spec.Snapshot
import CordialMiners.Spec.WeightedCertificate
import CordialMiners.Spec.ThresholdFinality
import CordialMiners.Ref.WeightedCollector
import CordialMiners.Spec.Blocklace
import CordialMiners.Spec.Equivocation
import CordialMiners.Spec.FinalLeader
