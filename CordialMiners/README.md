# PoR-weighted Cordial Miners, formalized in Lean 4

A machine-checked formalization of PoR-weighted Cordial Miners, a leaderless DAG-based BFT consensus
protocol. This is the next LeaTTa iteration, after the MeTTaIL formalization. It follows the blueprint
"LLM + Lean Guided Synthesis and Verification of PoR-Weighted Cordial Miners" (Goertzel), and takes the
formal content of that blueprint as the specification, not its process.

Everything here is held to the LeaTTa bar: no `sorry`, no `admit`, no `native_decide`, no `partial`, no
`unsafe`. Every headline theorem is axiom-clean (it depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`, never on `sorryAx`).

## What it proves, in one sentence

Under three named assumptions (a Byzantine-weight bound, honest non-equivocation, and finality
permanence), PoR-weighted Cordial Miners is safe: no two conflicting values are ever finalized, correct
miners never publish conflicting positions, and the blocklace stays well formed.

The headline theorem is `cm_end_to_end_safety_permanent` in `Proofs/EndToEndSafety.lean`.

## The headline result, built up in layers

The ordering's prefix-monotonicity (the property that lets all correct miners agree on one growing
order) is the hard part of consensus safety. We do not assume it. We derive it, in stages, from a single
primitive fact. Each `cm_end_to_end_safety_*` variant lets you enter at a different level:

```
cm_end_to_end_safety            takes abstract OutputMonotone as a hypothesis
        ⇑  tau_08_anchored_output_monotone        (Ref/AnchoredOrder)
cm_end_to_end_safety_anchored   assumes AnchorPrefixMonotone (the anchor sequence grows as a prefix)
        ⇑  finalizedAnchors_prefixMonotone        (Ref/FinalizedAnchors)
cm_end_to_end_safety_finalized  assumes the finalized-wave count is monotone (one scalar fact)
        ⇑  finalCountOf_monotone                  (Ref/FinalityPermanence)
cm_end_to_end_safety_permanent  assumes only finality permanence (a finalized wave stays finalized)
```

At the bottom, the whole safety story rests on three facts a BFT engineer already expects: the
Byzantine-weight bound, honest non-equivocation, and finality permanence.

## Layer map

The library is built in dependency order. A later layer may import an earlier one, never the reverse.

```
Foundation -> Spec -> Ref -> Trec -> Tfine -> CMIR -> Extract -> Sim -> Tests -> Proofs
```

- **Foundation**: weight and threshold arithmetic. The weighted-overlap lemma (`found_05_weighted_overlap`)
  is the safety keystone: two heavy signer sets overlap in more than the adversary's weight. Plus the
  prefix order for output discipline (`found_08_prefix_*`).
- **Spec**: the abstract protocol. Threshold finality and its self-enforcing safety
  (`cert_06_no_conflicting_threshold_finals`), the blocklace and equivocation
  (`bl_02_insert_parentClosed`, `bl_03_observes_*`, `bl_06_equiv_sound`), final-leader ratification
  (`fl_07_no_conflicting_ratifications`), the ordering contract and output consistency
  (`tau_09_output_consistent`), and the dissemination and scheduler safety specs.
- **Ref**: executable references. The weighted certificate collector (`collectorStep`, with its
  invariants), and a verified concrete topological-sort ordering (`topoSort`): deterministic,
  duplicate-free, output-valid, topologically sorted, and complete under a strict-rank acyclicity
  hypothesis. `BlockOrder` wires `topoSort` to the actual blocklace; `AnchoredOrder`, `FinalizedAnchors`,
  and `FinalityPermanence` are the leader-safety reduction chain.
- **Trec / Tfine**: the coarse rewrite theory with causal well-formedness (`trec_reachable_wf`), and the
  fine evidence-carrying theory with the abstraction map and forward simulation (`tfine_refines_trec`)
  that lifts coarse safety to the operational layer.
- **CMIR / Extract**: a MeTTa-IL atom IR and a lossless extraction. `extract_decode_encode` proves that
  decoding an encoded fact recovers it exactly.
- **Sim / Tests**: an executable end-to-end protocol run (`simulate`), and worked examples checked at
  build time with `decide`.
- **Proofs**: the top-level safety aggregate (`cm_end_to_end_safety` and its discharged variants).

## Theorem registry (selected)

| ID | Name | Meaning |
| --- | --- | --- |
| FOUND-05 | `found_05_weighted_overlap` | two heavy signer sets overlap above the adversary bound |
| CERT-06 | `cert_06_no_conflicting_threshold_finals` | no two valid threshold certificates carry conflicting values |
| BL-02 | `bl_02_insert_parentClosed` | extending with a parent-resolved block preserves closure |
| FL-07 | `fl_07_no_conflicting_ratifications` | no two valid ratification certificates ratify conflicting blocks |
| TAU-09 | `tau_09_output_consistent` | correct miners under a common limit produce prefix-comparable orders |
| TAU-08 | `tau_08_anchored_output_monotone` | the anchored ordering is output-monotone, from leader safety |
| (Trec) | `trec_reachable_wf` | every reachable coarse state respects the dependency chain |
| (Tfine) | `tfine_refines_trec` | the abstraction is a forward simulation, lifting coarse safety |
| (Extract) | `extract_decode_encode` | extraction to MeTTa-IL atoms is lossless |
| (top) | `cm_end_to_end_safety_permanent` | full safety from the three named primitives |

## Trusted boundaries (honest accounting)

These are stated as explicit hypotheses, faithful to the blueprint's design. They are assumptions, not
gaps in the proofs.

- **Finality permanence** enters the top theorem as a hypothesis: a finalized wave stays finalized as the
  blocklace grows. It is the blocklace-only-grows discipline applied to finality certificates.
- **Liveness** (dissemination completeness, scheduler non-starvation) is conditional on the network and
  scheduler fairness assumptions stated in `Spec/DisseminationSpec.lean` and `Spec/SchedulerSpec.lean`.
  The structural cores (FIFO fair-lane progress, bounded-service credit) are proved.
- Certificate persistence under blocklace extension (the approval relation is non-monotone) is future
  work, noted in `Spec/FinalLeader.lean`.
- Extraction targets MeTTa-IL atoms; a RholangCore target would follow the same encode/decode pattern.

## Build and verify

```
export PATH="$HOME/.elan/bin:$PATH"
lake build CordialMiners
```

The forbidden-token guard checks the bar:

```
bash scripts/ci/check-no-forbidden.sh
```

To check that a theorem is axiom-clean, print its axiom dependencies (you want to see only `propext`,
`Classical.choice`, `Quot.sound`, and never `sorryAx`):

```lean
import CordialMiners
open CordialMiners
#print axioms cm_end_to_end_safety_permanent
```

The executable parts run. For instance `#eval simulate demo` (in `Sim/Run.lean`) drives approvals
through the collector and orders the finalized blocks, printing `[1, 2, 3]`.
