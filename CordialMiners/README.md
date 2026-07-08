<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# PoR-weighted Cordial Miners, formalized in Lean 4

This directory contains the Lean formalization of PoR-weighted Cordial Miners, a leaderless DAG-based
BFT consensus protocol. The protocol source is Cordial Miners by Keidar, Naor, Poupko, and Shapiro. The
weighted Proof-of-Reputation variant follows Goertzel's blueprint. The blueprint supplies the target
specification, not the proof process.

The development is checked under the same bar as the rest of LeaTTa: no `sorry`, no `admit`, no
`native_decide`, no `partial`, and no `unsafe`. The public theorem audits print only Lean's standard
classical axioms, `propext`, `Classical.choice`, and `Quot.sound`. They never print `sorryAx`.

## What the top theorem says

Under three named assumptions, PoR-weighted Cordial Miners is safe. The assumptions are:

- the adversary is below the Byzantine-weight bound;
- honest participants do not equivocate;
- finality is permanent as the blocklace grows.

The conclusion is `EndToEndSafety`: no two conflicting values are finalized, correct miners do not
publish conflicting positions, and the blocklace remains well formed. The shared assumption bundle is
`EndToEndAssumptions`. The main theorem is:

```lean
end_to_end_safety_of_finality_permanence
```

The theorem lives in `Proofs/EndToEndSafety.lean`.

## How the proof is built

The ordering's prefix-monotonicity is not assumed. It is derived through the reduction chain below.

```text
end_to_end_safety_of_output_monotone          assumes OutputMonotone
        ^
tau_08_anchored_output_monotone               proves OutputMonotone from anchored leader safety
        ^
finalizedAnchors_prefixMonotone               proves anchored prefix monotonicity
        ^
finalCountOf_monotone                         proves monotone finalized-wave count
        ^
end_to_end_safety_of_finality_permanence      assumes finality permanence
```

The bottom of the chain is the part a BFT reader expects: threshold overlap from the Byzantine-weight
bound, honest non-equivocation, and finality permanence.

## Layer map

The library is ordered so later layers may import earlier layers, but not the reverse.

```text
Foundation -> Spec -> Ref -> Trec -> Tfine -> CMIR -> Extract -> Sim -> Runtime -> Tests -> Proofs
```

`Foundation` proves the weighted-overlap arithmetic and prefix-order facts. The key theorem is
`found_05_weighted_overlap`: two heavy signer sets overlap above the adversary bound.

`Spec` defines the abstract protocol contracts: threshold finality, blocklace closure, equivocation,
final-leader ratification, ordering consistency, dissemination, and scheduling. Examples include
`cert_06_no_conflicting_threshold_finals`, `bl_02_insert_parentClosed`, `bl_06_equiv_sound`,
`fl_07_no_conflicting_ratifications`, and `tau_09_output_consistent`.

`Ref` contains executable references. The certificate collector has invariants around `collectorStep`.
The concrete `topoSort` is deterministic, duplicate-free, output-valid, topologically sorted, and
complete under a strict-rank acyclicity hypothesis. `BlockOrder`, `AnchoredOrder`,
`FinalizedAnchors`, and `FinalityPermanence` form the leader-safety reduction chain.

`Trec` and `Tfine` define the coarse rewrite theory and the evidence-carrying fine theory. The coarse
theorem `trec_reachable_wf` preserves the dependency chain. The fine theorem `tfine_refines_trec` is a
forward simulation that lets coarse safety lift to the operational layer.

`CMIR` and `Extract` define a small MeTTaIL atom IR and prove lossless extraction. `extract_decode_encode`
recovers an encoded fact exactly. The runtime bridge adds `encodeFactA` and `decodeFactA` for the real
`MeTTaIL.AST`.

`Sim` and `Tests` contain executable examples checked during the build. `Runtime` hosts the coarse
protocol as a MeTTaIL presentation. `Proofs` assembles the top-level safety theorem.

## Runtime bridge

The runtime bridge hosts the coarse protocol as a MeTTaIL dialect. A configuration is:

```text
(cm inbox state)
```

The `inbox` and `state` children are AC collections with a `nil` sentinel. Proposal and ordering steps
are driven by input events:

```text
(ev-propose w h)  ->  (propose w h)
(ev-order hs)     ->  (ordered-prefix hs)
```

The derived rules add facts along this chain:

```text
propose -> q-approve -> cert-threshold -> final -> final-leader
```

Run the runtime examples with:

```bash
lake build CordialMiners.Runtime.Run
```

Expected checks:

```text
info: CordialMiners/Runtime/Run.lean:88:0: true
info: CordialMiners/Runtime/Run.lean:121:0: true
info: CordialMiners/Runtime/Run.lean:223:0: true
```

Those checks cover a buried proposal event, an ordered-prefix event with an encoded list payload, and a
five-step path from one proposal event to `final-leader`. The file also proves relation witnesses:
`buriedProposal_eval_modAC`, `order_eval_modAC`, and `finality_eval_run_modAC`.

The forward theorem says every coarse `TrecState.Step` has a runtime witness:

```lean
trec_step_forward_decode :
  TrecState.Step s s' ->
  ∃ events target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    astToState dW dH target = s'
```

The backward theorem says every shaped runtime step, modulo AC, decodes to a coarse step or a decoded
stutter, provided the field decoders respect runtime AC-equivalence:

```lean
runtime_step_backward_of_decoders_acEq :
  (∀ {a b}, ACEq acOpCM a b -> dW a = dW b) ->
  (∀ {a b}, ACEq acOpCM a b -> dH a = dH b) ->
  RuntimeConfigShape source ->
  RewStepModAC acOpCM cmPresentation source target ->
  TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
    astToState dW dH source = astToState dW dH target
```

The executable Nat/Nat instance proves the decoder condition as `dNat_acEq` and instantiates the theorem
as `runtime_step_backward_nat`. A theorem for arbitrary raw decoders is not claimed. Such decoders can
distinguish AC-equivalent payloads.

The transfer theorems `trec_step_forward_reachable` and `trec_step_forward_wf` show that the runtime
witness produced by the forward theorem decodes to a reachable, well-formed coarse state when the source
is reachable. The concrete finality run has `finality_runtime_trec_reachable`, `finality_runtime_wf`, and
`finality_runtime_final_needs_propose`.

Read `Runtime/README.md` for the proof shape, file map, exact checks, and source notes.

## Selected theorem names

The names below are the usual entry points when checking the development.

```text
Foundation
  found_05_weighted_overlap
  found_08_prefix_refl
  found_08_prefix_trans

Spec
  cert_06_no_conflicting_threshold_finals
  bl_02_insert_parentClosed
  bl_06_equiv_sound
  fl_07_no_conflicting_ratifications
  tau_09_output_consistent

Ref
  tau_08_anchored_output_monotone
  finalizedAnchors_prefixMonotone
  finalCountOf_monotone
  topoSort_valid

Trec and Tfine
  trec_reachable_wf
  tfine_refines_trec

Extraction
  extract_decode_encode
  decodeFactA_encodeFactA
  astToState_encConfig

Runtime
  runtimeConfigShape_encConfig
  runtimeConfigShape_acEq_iff
  noEmbeddedConfig_not_rewStepModAC
  runtimeConfigShape_rewStepModAC_top
  astToState_acEq_of_decoders_acEq
  runtime_step_backward_of_decoders_acEq
  runtime_step_backward_nat
  trec_step_forward_decode
  trec_step_forward_reachable
  trec_step_forward_wf
  scoped_runtime_bridge

Executable runtime checks
  buriedProposal_eval_modAC
  order_eval_modAC
  finality_eval_run_modAC
  finality_runtime_wf
  finality_runtime_final_needs_propose

Top result
  end_to_end_safety_of_finality_permanence
```

## Scope boundaries

The assumptions are explicit.

Finality permanence enters the top theorem as a hypothesis. It is the blocklace-only-grows discipline
applied to finality certificates.

Liveness depends on network and scheduler fairness assumptions stated in `Spec/DisseminationSpec.lean`
and `Spec/SchedulerSpec.lean`. The structural pieces, FIFO fair-lane progress and bounded-service credit,
are proved.

Certificate persistence under blocklace extension remains future work because the approval relation is
non-monotone. The note is in `Spec/FinalLeader.lean`.

The runtime bridge covers encoded redexes, executable demos, the decoded forward theorem, head-rule and
direct-step backward classifiers, the generic AC-stable decoder theorem, the executable Nat/Nat theorem,
and the named stutter fragments. More field codecs need their own AC-stability proofs, or a stronger
shape invariant.

Extraction targets MeTTaIL atoms and the real MeTTaIL AST. A RholangCore target would follow the same
encode/decode pattern.

## Build and verify

Build the whole Cordial Miners layer:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build CordialMiners
```

Run the forbidden-token guard:

```bash
bash scripts/ci/check-no-forbidden.sh
```

Check the public axiom surface:

```bash
lake build CordialMiners.AxiomAudit
lake build CordialMiners.Runtime.AxiomAudit
```

The audit output should list only `propext`, `Classical.choice`, and `Quot.sound`.

The older executable protocol demo is still present:

```lean
#eval simulate demo
```

`Sim/Run.lean` prints:

```text
[1, 2, 3]
```

## Sources

The consensus side follows:

- Keidar, Naor, Poupko, and Shapiro, Cordial Miners.
- Goertzel's PoR-weighted Cordial Miners blueprint.

The runtime bridge follows:

- Meseguer's rewriting logic;
- the Maude account of rewriting modulo equations;
- the Chemical Abstract Machine multiset model;
- Lamport's stuttering-insensitive account of TLA behavior;
- the AC-matching literature cited in the Verso book.
