<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Cordial Miners on the MeTTaIL runtime

This directory turns the coarse Cordial Miners protocol into a MeTTaIL dialect. The bridge does not call
the older shallow `Sexpr` simulator. It encodes facts, input events, and whole configurations as
`MeTTaIL.AST`, declares the six coarse protocol rules in `cmPresentation`, and runs them with the
AC-aware runtime engine.

Run the executable checks first:

```bash
lake build CordialMiners.Runtime.Run
```

Expected output:

```text
info: CordialMiners/Runtime/Run.lean:88:0: true
info: CordialMiners/Runtime/Run.lean:121:0: true
info: CordialMiners/Runtime/Run.lean:223:0: true
Build completed successfully
```

Those three checks cover the cases the bridge is meant to handle:

- a proposal event buried inside an AC inbox;
- an ordered-prefix event whose payload is an encoded AST list;
- a five-step run from one proposal event to `final-leader`.

The same file proves relation witnesses for the computed results:
`buriedProposal_eval_modAC`, `order_eval_modAC`, and `finality_eval_run_modAC`.

## Runtime shape

A configuration is one AST node:

```text
(cm inbox state)
```

Both children are binary collections. `acOpCM` marks the `inbox` and `state` labels as associative and
commutative. There is no identity law in the runtime AC theory, so each collection ends in the sentinel
leaf `nil`.

A proposal input event is:

```text
(ev-propose w h)
```

When the proposal rule fires, the event is consumed and the state gains:

```text
(propose w h)
```

The derived rules extend the state along this chain:

```text
propose -> q-approve -> cert-threshold -> final -> final-leader
```

The AST state is a multiset. The coarse `TrecState` is a `Finset`. Decoding collapses duplicate facts,
so a concrete runtime step can be a decoded stutter.

## Files

- `Encode.lean` defines `encodeFactA`, `decodeFactA`, `encodeEventA`, `decodeEventA`, `encState`,
  `encInbox`, `encConfig`, `astToInbox`, and `astToState`.
- `Presentation.lean` defines `acOpCM`, `cmPresentation`, and the six runtime rewrite rules.
- `Simulation.lean` proves the forward bridge, the backward step refinement, and the transfer lemmas.
- `Run.lean` contains the executable Nat/Nat examples.
- `AxiomAudit.lean` prints the axiom dependencies for the runtime theorem surface.

## Forward bridge

Every coarse protocol step can be reproduced by the runtime. The theorem is:

```lean
trec_step_forward_decode :
  TrecState.Step s s' ->
  ∃ events target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    astToState dW dH target = s'
```

Proposal and ordering steps get a one-event inbox. The derived rules use the current state and no new
input event.

The target is compared through `astToState`, not by literal AST equality. Runtime collections are AC
multisets, while coarse states are finite sets. If a rule adds a fact that already decodes to a fact in
the coarse state, the AST changes and the decoded state does not.

The named duplicate and undecodable-insertion stutter lemmas are:

- `decodeStateA_cons_encodeFactA_stutter`
- `astToState_cons_encodeFactA_stutter`
- `event_forward_stutter`
- `derived_step_forward_stutter`
- `event_inbox_mem_forward_stutter`
- `derived_state_mem_forward_stutter`
- `decodeStateA_stateA_none`

If the source coarse state is reachable, `trec_step_forward_reachable` shows that the decoded target of
the runtime witness is reachable. `trec_step_forward_wf` adds the coarse dependency invariant. The
five-step executable run uses the same idea in `finality_runtime_trec_reachable` and `finality_runtime_wf`.

## Backward bridge

The backward theorem is a stuttering step refinement from shaped runtime configurations to `TrecState`.
It is stated for field decoders that respect runtime AC-equivalence:

```lean
runtime_step_backward_of_decoders_acEq :
  (∀ {a b}, ACEq acOpCM a b -> dW a = dW b) ->
  (∀ {a b}, ACEq acOpCM a b -> dH a = dH b) ->
  RuntimeConfigShape source ->
  RewStepModAC acOpCM cmPresentation source target ->
  TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
    astToState dW dH source = astToState dW dH target
```

The proof has four layers.

1. `runtimeConfigShape_rewStepModAC_top` moves a modulo-AC step from a shaped configuration to a top-level
   `cm` redex in the representative selected by `RewStepModAC`.
2. `runtime_root_step_backward` classifies the six presentation rules.
3. `runtime_step_direct` handles contextual closure after the shape invariant rules out inner runtime
   redexes.
4. `astToState_acEq_of_decoders_acEq` transports the decoded state across the source and target AC
   equalities.

The executable Nat/Nat instance proves the field-decoder condition as `dNat_acEq`. From that it derives:

```lean
runtime_step_backward_nat :
  RuntimeConfigShape source ->
  RewStepModAC acOpCM cmPresentation source target ->
  TrecState.Step (astToState dNat dNat source) (astToState dNat dNat target) ∨
    astToState dNat dNat source = astToState dNat dNat target
```

A theorem for arbitrary raw decoders is not stated. Such a decoder could distinguish two AC-equivalent
payloads, so that statement would be false. A new concrete codec should prove the same field-decoder
stability that `dNat_acEq` proves for `Nat`.

## AC matcher boundary

`MeTTaILProofs/ACMatch.lean` implements only the AC matching fragment this presentation uses: one fixed
subpattern and one rest variable under a binary AC collection. That fragment is enough to find a fact or
event anywhere inside `state` or `inbox`.

The public theorem names are:

- `matchPatAC_acRest_sound`
- `matchPatAC_acRest_complete_of_flat_split`
- `matchPatAC_acRest_complete_of_fresh_split`
- `matchPatAC_sound`
- `oneStepAC'_sound`
- `evalAC'_sound`

The fresh-split theorem is the one that matches the protocol rule shape. Once the fixed leaf matches, a
fresh rest variable binds to the rebuilt complement. Full relation completeness for the whole matcher is
not claimed.

## Checks

Build the simulation layer:

```bash
lake build CordialMiners.Runtime.Simulation
```

Build the runtime axiom audit:

```bash
lake build CordialMiners.Runtime.AxiomAudit
```

The audit output should list only `propext`, `Classical.choice`, and `Quot.sound`. It must not list
`sorryAx`.

## Sources

The protocol side follows Cordial Miners by Keidar, Naor, Poupko, and Shapiro. The PoR-weighted variant
follows Goertzel's blueprint.

The runtime bridge follows Meseguer's rewriting logic account of systems as equations plus rules, Maude's
execution model for rewriting modulo equations, and the multiset style of the Chemical Abstract Machine.
The stutter clause follows Lamport's account of stuttering-insensitive behavior in TLA.

The Verso chapter cites these sources directly in `book/Docs/CordialMiners.lean`; the bibliography entries
are in `book/Docs/Papers.lean`.
