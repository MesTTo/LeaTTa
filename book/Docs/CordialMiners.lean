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
with no leader and no extra voting rounds. This chapter is about a third Lean development in this book,
built alongside the MeTTa kernel and {ref "sec-mettail"}[the MeTTaIL framework], that formalizes the
*PoR-weighted* (Proof-of-Reputation) variant of the protocol, following a blueprint by Ben Goertzel.

The earlier chapters formalize languages. This one formalizes the layer underneath a language on a
chain: the part that lets many nodes agree on one order of events. The motivation is the same thread
that runs through the rest of the book. The MeTTa operational-semantics paper {citep mops}[] and the
Hyperon program {citep goertzelMetagraph}[] call for a machine-checked specification that an
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
integer inequality with no division and no rounding.

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
canonical tie-breaking. It is written as structural recursion on a fuel counter equal to the vertex
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

So the whole edifice comes to rest on three facts a BFT engineer already expects: the Byzantine-weight
bound, honest non-equivocation, and finality permanence. The development exposes the theorem at each
level of this reduction, so you can enter it wherever you are willing to assume.

# Extraction, and Running It

The coarse facts extract to MeTTa-IL atoms, the same intermediate language as {ref "sec-mettail"}[the
MeTTaIL chapter]. We prove the extraction is lossless: decoding an encoded fact recovers it exactly,
including the variable-length ordered-prefix list. The executable parts run, too. A worked simulation
folds approvals through the weighted certificate collector to decide finality, keeps the finalized
blocks, and orders them with the verified topological sort, and a build-time check confirms the published
order on a small example.

# What Is Left Open, Honestly

The boundaries are stated as explicit hypotheses, faithful to the blueprint, not papered over. Finality
permanence enters the top theorem as a hypothesis, which is the canonical safety primitive the residual
rests on. Liveness, that dissemination eventually delivers and that the scheduler does not starve a
runnable wave, is conditional on network and scheduler fairness, and we prove the structural cores
(FIFO fair-lane progress and bounded-service credit) while leaving the temporal argument to its
assumptions. Certificate persistence under blocklace extension, where the approval relation is
non-monotone, is future work. Extraction targets MeTTa-IL atoms here, and a RholangCore target would
follow the same lossless encode-and-decode pattern.
