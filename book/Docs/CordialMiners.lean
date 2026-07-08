-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
LeaTTa: Chapter: PoR-weighted Cordial Miners, formalized.
-/
import VersoManual
import Illuminate
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "PoR-Weighted Cordial Miners: Machine-Checked Consensus Safety" =>
%%%
tag := "sec-cordial-miners"
%%%

Cordial Miners is a leaderless DAG-based BFT consensus protocol {citep cordialMiners}[]. Participants
gossip signed blocks that point back at the blocks they have seen, the blocks form a growing DAG (a
*blocklace*), and each participant reads a total order of events out of its own local copy of that DAG,
with no leader and no extra voting rounds. The chapter covers a third Lean development in this book,
built alongside the MeTTa kernel and {ref "sec-mettail"}[the MeTTaIL framework], that formalizes the
*PoR-weighted* (Proof-of-Reputation) variant of the protocol, following a blueprint by Ben Goertzel.

The earlier chapters formalize languages. The consensus chapter formalizes the layer underneath a
language on a chain: the part that lets many nodes agree on one order of events. The motivation is the
same thread that runs through the rest of the book. The MeTTa operational-semantics paper {citep mops}[]
and the Hyperon program {citep goertzelMetagraph}[] call for a machine-checked specification that an
implementation can be certified against. For a consensus protocol the property you most want certified
is *safety*: two honest nodes never commit conflicting orders. That is what we prove, and we prove it
down to a small set of named assumptions a consensus engineer already expects.

Everything here is held to the same bar as the rest of the development. There is no `sorry`, `admit`,
`native_decide`, `partial`, or `unsafe`, a CI guard enforces it, and an axiom audit shows every
headline theorem depends only on the three standard axioms ({citep mathlib}[]).

# The Blocklace and Threshold Finality

The blocklace is a finite set of signed blocks. Each block records its creator, wave, round, slot, the
hashes of its parents, and its own hash. Two blocks *conflict* when the same creator made them in the
same slot with different hashes, which is the equivocation a Byzantine participant might attempt. A
local blocklace is *parent-closed* when every block's parents are also present, and inserting a block
whose parents are already there preserves closure. Observation, reading a block's causal past by
following parent pointers, is the reflexive-transitive closure of the parent edge.

"PoR-weighted" means participants are not counted, they are weighed. Each participant carries a weight,
a reputation projection the framework treats as an abstract nonnegative parameter, and a set of
participants is *heavy* when its total weight crosses a rational threshold of the committee weight. We
keep all arithmetic over the natural numbers and compare cross-products, so a heaviness test is an
integer inequality with no division and no rounding. The separate identity-indexed reputation note
explains how signed capability judgments and observed traces can justify such weights
{citep reputationFramework}[]. The Lean development here does not formalize that reputation calculus; it
takes the weight function as input and proves what the consensus protocol needs from it.

The whole safety story rests on one arithmetic fact about heavy sets. If two sets are each heavier than
the threshold, their overlap is heavier than twice the threshold minus the whole, so under a Byzantine
bound the overlap must contain an honest participant. Stated over plain naturals, the heart of it is
short enough to check as you read it:

```lean
-- The Nat-safe weighted-overlap inequality, the safety keystone in miniature.
-- a, c are the two heavy weights; b the adversary bound; d, e, f the overlap terms.
example (a b c d e f : Nat) (hA : b < a) (hB : b < c) (key : f + d = a + c) (hud : f ≤ e) :
    2 * b < d + e := by omega
```

From this keystone follows the chapter's first safety theorem, threshold finality. Two valid threshold
certificates for the same committee cannot carry conflicting values, because their heavy signer sets
overlap in an honest participant who would then have signed both. Threshold finality is therefore
self-enforcing: it needs no liveness or health assumption, only the adversary bound and that honest
participants do not equivocate.

# Equivocation and Final Leaders

A block *approves* a target when it observes the target and observes no conflict with it. A creator
*ratifies* a target when one of its blocks approves it, and a ratification certificate is a threshold
certificate whose signers are ratifying creators. Because ratification is weighted threshold approval,
the no-conflicting-ratifications result is a direct corollary of threshold finality: under the
Byzantine bound and honest non-equivocation, two valid ratification certificates cannot ratify
conflicting target blocks. Final leaders are the anchors the order is read off from, so this is the
safety of leader selection.

# A Deterministic Order, Computed and Verified

For all nodes to agree, the function that reads an order out of a blocklace must be deterministic and
must respect causality. We give a concrete, computable one: a topological sort of the present hashes by
the parent graph, in the style of Kahn's algorithm, choosing the least available hash at each step for
canonical tie-breaking. The algorithm is written as structural recursion on a fuel counter equal to the vertex
count, so it is total without `partial`.

We prove the order is deterministic (it is a pure function), has no duplicates, lists only hashes that
are present, and is topologically sorted: no dependency is ever placed after the block that depends on
it. Under a strict rank on the parent graph (a parent ranks below its child, as block rounds do) it is
also complete, so it lists exactly the present hashes, once each. Wiring this to the blocklace gives a
concrete ordering for which a block's parents never come after it, the causal-consistency guarantee
stated against the protocol's own parent relation.

A separate consistency result is what ties two honest nodes together. If two local blocklaces both sit
inside one larger limit blocklace, and the order is prefix-monotone in the blocklace, then the two
orders are prefix-comparable: one is a prefix of the other, so the nodes never publish a conflicting
position. Prefix-monotonicity is the hard, leader-safety-dependent property, and the last section
explains how we discharge it rather than assume it.

# Two Theories and a Simulation

The protocol is modeled at two levels. The coarse theory records evidence-free facts (a proposal
exists, a certificate exists, a leader is final) and a step relation that only ever adds facts. We
prove every reachable coarse state is causally well formed: a final fact is always backed by the
proposal it descends from. The fine theory carries the operational evidence the coarse theory drops,
the actual signer sets behind each certificate, and an abstraction map forgets that evidence.

The abstraction is a forward simulation: every fine step is matched by a coarse step or leaves the
abstraction unchanged, so reachability transfers and the coarse safety lifts to the evidence-carrying
operational layer. The proof-friendly theory governs the realistic one, which is the point of building
both.

# End-to-End Safety, Reduced to Three Facts

The top theorem composes the pieces: under the standard assumptions the protocol guarantees
leader-agreement, output consistency, and blocklace integrity, in one statement. The interesting work
is the ordering's prefix-monotonicity, the property that lets every honest node agree on one growing
order. We do not assume it. We derive it in stages, each turning an assumption into a theorem.

The real order concatenates, in finalized-leader sequence, each anchor's fixed committed history. If
the anchor sequence grows as a prefix as the blocklace grows, the output can only be appended to, never
reordered, so it is prefix-monotone. The anchor sequence grows as a prefix when the count of
consecutively finalized waves only grows. That count only grows when finality is *permanent*, a
finalized wave stays finalized as the blocklace grows, which is the blocklace-only-grows discipline
applied to finality certificates.

The safety chain rests on three facts a BFT engineer already expects: the Byzantine-weight bound,
honest non-equivocation, and finality permanence. The development names the shared assumptions
`EndToEndAssumptions` and the shared conclusion `EndToEndSafety`, then exposes the theorem at each
level of this reduction, so you can enter it wherever you are willing to assume. The Lean names follow
that reduction:
`end_to_end_safety_of_output_monotone`,
`end_to_end_safety_of_anchor_prefix_monotone`,
`end_to_end_safety_of_finalized_count_monotone`, and
`end_to_end_safety_of_finality_permanence`.

# Extraction, and Running It

The coarse facts extract to MeTTaIL atoms, the same intermediate language as {ref "sec-mettail"}[the
MeTTaIL chapter]. We prove the extraction is lossless: decoding an encoded fact recovers it exactly,
including the variable-length ordered-prefix list. The executable parts run, too. A worked simulation
folds approvals through the weighted certificate collector to decide finality, keeps the finalized
blocks, and orders them with the verified topological sort, and a build-time check confirms the published
order on a small example.

# Hosting the Protocol on the MeTTaIL Runtime

The runtime bridge is the place where the dialect story becomes concrete. The coarse Cordial Miners rules
are encoded as a MeTTaIL presentation. The verified runtime executes that presentation directly.

A runtime configuration is the AST node:

```
(cm inbox state)
```

The `inbox` and `state` fields are binary collections. Their labels are flagged as associative and
commutative, and both collections end in a `nil` sentinel. The encoding follows the rewriting-logic view of a
system as equations plus rules
{citep meseguerRewritingLogic}[] and the Maude execution pattern for rewriting modulo structural
equations {citep maudeBook}[]. The same choice matches the Chemical Abstract Machine's multiset picture
{citep chemicalAbstractMachine}[]: the facts form a soup, and a rule fires when the soup contains the
pieces it needs.

The two spontaneous coarse rules become executable through the inbox. A proposal event `(ev-propose w h)`
is consumed and the state gains `(propose w h)`. An ordering event `(ev-order hs)` is consumed and the
state gains `(ordered-prefix hs)`. The remaining rules extend the state along this chain:

```
propose -> q-approve -> cert-threshold -> final -> final-leader
```

The codecs are lossless on the encoded fragment. `decodeEventA_encodeEventA` recovers one encoded event.
`decodeInboxA_encInbox` recovers an encoded inbox. `astToInbox_encConfig` recovers the inbox part of a
configuration. `astToState_encConfig` recovers the finite coarse state.

The file `CordialMiners/Runtime/Run.lean` gives three build-checked examples:

```
#eval oneStepAC' acOpCM cmPresentation buriedProposalStart == some afterBuriedProposal
#eval evalAC' acOpCM cmPresentation 1 orderStart == afterOrder
#eval evalAC' acOpCM cmPresentation 5 finalityStart == finalityExpectedConfig
```

All three evaluate to `true` during the build. The buried-proposal example checks that the matcher can
find an event that is not at the head of the inbox. The ordering example checks the explicit AST-list
payload. The finality example consumes one proposal and reaches `final-leader` in five runtime steps.
Theorems `buriedProposal_eval_modAC`, `order_eval_modAC`, and `finality_eval_run_modAC` give relation
witnesses for those computed results.

The AC matcher has a narrow scope. Full AC matching has hard cases even in restricted elementary forms
{citep ekerSingleACMatching}[], and variadic matching with sequence variables needs a larger theory
{citep variadicACMatching}[]. The runtime rules need one fixed subpattern and one rest variable under a
binary AC collection. That is the fragment proved in `MeTTaILProofs/ACMatch.lean`.

The theorem `matchPatAC_acRest_sound` says that a successful fragment match has an AC-equivalent
representative accepted by ordinary matching. `matchPatAC_acRest_complete_of_flat_split` proves
completeness for a chosen flattened split. `matchPatAC_acRest_complete_of_fresh_split` packages the
protocol rule shape: the fixed leaf matches, and a fresh rest variable binds to the rebuilt complement.
`matchPatAC_sound`, `oneStepAC'_sound`, and `evalAC'_sound` lift the soundness result to the executable
matcher, stepper, and evaluator. Full relation completeness beyond this linear fragment is not claimed.

The main relation theorem is forward completeness up to decoding. From a coarse step,
`trec_step_forward_decode` produces an inbox and a runtime target:

```
TrecState.Step s s' ->
∃ events target,
  RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
  astToState dW dH target = s'
```

The target is compared through `astToState`, not by literal AST equality. The runtime state is an AC
multiset with a `nil` sentinel. The protocol state is a `Finset`. Re-firing a rule can add a duplicate AST
fact, while the decoded finite set is unchanged. That equality branch is the stuttering abstraction used
in TLA-style refinement arguments {citep lamportTLA}[].

The duplicate cases are explicit. `decodeStateA_cons_encodeFactA_stutter` and
`astToState_cons_encodeFactA_stutter` state the basic fact-insertion stutter. `event_forward_stutter` and
`derived_step_forward_stutter` lift it to input and derived runtime steps. The list-level versions are
`event_inbox_mem_forward_stutter` and `derived_state_mem_forward_stutter`. The theorem
`decodeStateA_stateA_none` covers inserted leaves that are invisible to the selected decoder.

The backward theorem is the local step refinement in the other direction. The theorem is phrased for
field decoders that respect `ACEq acOpCM`:

```
runtime_step_backward_of_decoders_acEq :
  RuntimeConfigShape source ->
  RewStepModAC acOpCM cmPresentation source target ->
  TrecState.Step (astToState dW dH source) (astToState dW dH target) ∨
    astToState dW dH source = astToState dW dH target
```

The omitted hypotheses in that display are the two field-decoder AC-stability assumptions. A theorem for
arbitrary raw decoders is not stated. Such a decoder can distinguish two AC-equivalent payloads, so the
statement would be false.

The proof first moves to the representative chosen by `RewStepModAC`.
`runtimeConfigShape_acEq_iff` transports the shape invariant to that representative.
`noEmbeddedConfig_not_rewStepModAC` rules out hidden runtime steps inside clean payloads.
`runtimeConfigShape_rewStepModAC_top` reduces the step to a top-level `cm` redex, and
`runtime_root_step_backward` classifies the six rules. The generic transport lemma
`astToState_acEq_of_decoders_acEq` supplies the final AC-invariance step.

For the executable Nat/Nat instance, the field decoder proof is `dNat_acEq`. The proof gives
`astToState_dNat_acEq` and the concrete theorem `runtime_step_backward_nat`. That theorem is the runtime
claim most directly tied to the build-checked examples.

The forward witness also carries transfer results. If the source coarse state is reachable,
`trec_step_forward_reachable` proves that the decoded runtime target is reachable. `trec_step_forward_wf`
then applies `trec_reachable_wf` to that decoded target. The executable finality run has matching
corollaries: `finality_runtime_trec_reachable`, `finality_runtime_wf`, and
`finality_runtime_final_needs_propose`.

# What Remains Open

The boundaries are stated as explicit hypotheses. Finality permanence enters the top theorem as a
hypothesis. Finality permanence is the blocklace-only-grows discipline applied to finality certificates.

Liveness remains conditional on network and scheduler fairness. The development proves the structural
cores, FIFO fair-lane progress and bounded-service credit, but it does not prove a temporal dissemination
theorem.

Certificate persistence under blocklace extension remains future work because the approval relation is
non-monotone. Extraction targets MeTTaIL atoms and the real MeTTaIL AST here. A RholangCore target would
follow the same lossless encode-and-decode pattern.

The MeTTaIL runtime bridge proves the encoded redexes, executable demos, decoded forward theorem,
head-rule and direct-step backward classifiers, the generic AC-stable decoder backward theorem, the
executable Nat/Nat modulo-AC theorem, and named stutter fragments above. More field codecs need their own
AC-stability proofs, or a stronger shape invariant.
