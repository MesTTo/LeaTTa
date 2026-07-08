-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Distributed.DAS
Layer: Distributed
Purpose: Active Lean model of the distributed atomspace slice: vector clocks, mutation events,
  replica-local atom storage, issue and delivery steps, read-own-writes, mid-flight divergence,
  barrier extension under a named fair-delivery assumption, and quiescent convergence as per-event
  coverage. Full observable atom-set equality is stated only under explicit ordered-replay
  assumptions, because ordered lists do not commute by themselves.
Imports: MettaHyperonFull.Core.Space
Trusted boundary: none. Network fairness and ordered replay are theorem parameters, not Lean axioms.
Main exports: VectorClock, MutationEvent, Replica, System, Step, StepStar, FairDeliveryFrom,
  readOwnWrites, midFlightDivergence, eventualDelivery, barrierExtensionViaEventualDelivery,
  dasConvergence, sigmaConvergence, convergedMatchingBehavior
Open obligations: directional happens-before ordering and unordered CRDT quotient convergence remain
  future theorem refinements.
-/
import MettaHyperonFull.Core.Space

namespace Metta
namespace Distributed

abbrev ReplicaId := Nat
abbrev VectorClock := List Nat

/-- Read a vector-clock component. Missing components read as zero. -/
def vcGet (vc : VectorClock) (i : ReplicaId) : Nat := vc.getD i 0

/-- Increment one vector-clock component, leaving out-of-range clocks unchanged. -/
def vcIncAt : VectorClock -> ReplicaId -> VectorClock
  | [], _ => []
  | n :: rest, 0 => (n + 1) :: rest
  | n :: rest, i + 1 => n :: vcIncAt rest i

/-- The initial all-zero vector clock for a fixed replica count. -/
def vcZero (replicaCount : Nat) : VectorClock := List.replicate replicaCount 0

/-- Component-wise pairwise max. Differing-length clocks preserve the longer suffix. -/
def vcMax : VectorClock -> VectorClock -> VectorClock
  | [], vc => vc
  | vc, [] => vc
  | n1 :: rest1, n2 :: rest2 => Nat.max n1 n2 :: vcMax rest1 rest2

/-- Component-wise order, restricted to the known replica count. -/
def vcLe (replicaCount : Nat) (vc1 vc2 : VectorClock) : Prop :=
  forall i, i < replicaCount -> vcGet vc1 i <= vcGet vc2 i

/-- Component-wise equality, restricted to the known replica count. -/
def vcEq (replicaCount : Nat) (vc1 vc2 : VectorClock) : Prop :=
  forall i, i < replicaCount -> vcGet vc1 i = vcGet vc2 i

/-- Strict vector-clock order. -/
def vcLt (replicaCount : Nat) (vc1 vc2 : VectorClock) : Prop :=
  vcLe replicaCount vc1 vc2 /\ Not (vcEq replicaCount vc1 vc2)

theorem vcLeRefl (replicaCount : Nat) (vc : VectorClock) : vcLe replicaCount vc vc := by
  intro i _
  exact Nat.le_refl _

theorem vcLeTrans {replicaCount : Nat} {vc1 vc2 vc3 : VectorClock}
    (h12 : vcLe replicaCount vc1 vc2) (h23 : vcLe replicaCount vc2 vc3) :
    vcLe replicaCount vc1 vc3 := by
  intro i hi
  exact Nat.le_trans (h12 i hi) (h23 i hi)

theorem vcEqRefl (replicaCount : Nat) (vc : VectorClock) : vcEq replicaCount vc vc := by
  intro i _
  rfl

theorem vcLeAntisym {replicaCount : Nat} {vc1 vc2 : VectorClock}
    (h12 : vcLe replicaCount vc1 vc2) (h21 : vcLe replicaCount vc2 vc1) :
    vcEq replicaCount vc1 vc2 := by
  intro i hi
  exact Nat.le_antisymm (h12 i hi) (h21 i hi)

/-- Mutation kinds modeled by the distributed atomspace state machine. Replacement can be modeled as
    remove then add. -/
inductive MutationKind where
  | add
  | remove
  deriving Repr, BEq, Inhabited

/-- A mutation event records the target atom, the origin replica, and the origin's vector clock after
    the local increment. -/
structure MutationEvent where
  kind : MutationKind
  atom : Atom
  origin : ReplicaId
  clock : VectorClock
  deriving Repr, BEq, Inhabited

abbrev DASAtomSet := List Atom

/-- Remove the first runtime-equivalent atom from a replica-local atom multiset. -/
def removeFirstAtom (a : Atom) : DASAtomSet -> DASAtomSet
  | [] => []
  | x :: xs => if Atom.equiv x a then xs else x :: removeFirstAtom a xs

/-- Apply one mutation event to a replica-local atom multiset. -/
def applyEventToSet (sigma : DASAtomSet) (event : MutationEvent) : DASAtomSet :=
  match event.kind with
  | MutationKind.add => sigma ++ [event.atom]
  | MutationKind.remove => removeFirstAtom event.atom sigma

/-- Replay an application-order event log into an atom multiset. -/
def replayEvents (events : List MutationEvent) : DASAtomSet :=
  events.foldl applyEventToSet []

/-- A replica carries local atoms, its installed vector clock, and the events it has applied in
    application order. -/
structure Replica where
  id : ReplicaId
  sigma : DASAtomSet
  clock : VectorClock
  applied : List MutationEvent
  deriving Repr, BEq, Inhabited

def initialReplica (replicaCount : Nat) (id : ReplicaId) : Replica :=
  { id := id, sigma := [], clock := vcZero replicaCount, applied := [] }

/-- A distributed atomspace system: indexed replicas plus the global issued-event log. -/
structure System where
  replicas : List Replica
  log : List MutationEvent
  deriving Repr, BEq, Inhabited

def System.replicaCount (sys : System) : Nat := sys.replicas.length

/-- Lookup a replica by index. Out-of-range reads return a fresh empty replica with a matching id. -/
def replicaAt (sys : System) (id : ReplicaId) : Replica :=
  sys.replicas.getD id (initialReplica sys.replicaCount id)

def eventsAppliedAt (id : ReplicaId) (sys : System) : List MutationEvent :=
  (replicaAt sys id).applied

def hasApplied (id : ReplicaId) (event : MutationEvent) (sys : System) : Prop :=
  event ∈ eventsAppliedAt id sys

def localSpaceAt (sys : System) (id : ReplicaId) : Space :=
  ⟨(replicaAt sys id).sigma⟩

def matchesAt (sys : System) (id : ReplicaId) (pattern : Atom) : List Bindings :=
  (localSpaceAt sys id).query pattern

/-- The event a replica would issue from its current local clock. -/
def issuedEvent (sys : System) (id : ReplicaId) (kind : MutationKind) (atom : Atom) :
    MutationEvent :=
  let replica := replicaAt sys id
  { kind := kind, atom := atom, origin := id, clock := vcIncAt replica.clock id }

/-- Locally issue a mutation. The origin applies it immediately and appends it to the global log. -/
def issue (sys : System) (id : ReplicaId) (kind : MutationKind) (atom : Atom) : System :=
  let replica := replicaAt sys id
  let event := issuedEvent sys id kind atom
  let nextReplica :=
    { id := id,
      sigma := applyEventToSet replica.sigma event,
      clock := event.clock,
      applied := replica.applied ++ [event] }
  { replicas := sys.replicas.set id nextReplica, log := sys.log ++ [event] }

/-- Deliver a previously issued event to a remote replica. Preconditions live in `Step`. -/
def deliver (sys : System) (id : ReplicaId) (event : MutationEvent) : System :=
  let replica := replicaAt sys id
  let nextReplica :=
    { id := id,
      sigma := applyEventToSet replica.sigma event,
      clock := vcMax replica.clock event.clock,
      applied := replica.applied ++ [event] }
  { replicas := sys.replicas.set id nextReplica, log := sys.log }

/-- Causal deliverability in the vector-clock protocol. -/
def causallyDeliverable (event : MutationEvent) (replica : Replica) : Prop :=
  vcGet event.clock event.origin = vcGet replica.clock event.origin + 1 /\
    forall k, k ≠ event.origin -> vcGet event.clock k <= vcGet replica.clock k

def hbDAS (replicaCount : Nat) (e1 e2 : MutationEvent) : Prop :=
  vcLt replicaCount e1.clock e2.clock

/-- One distributed atomspace step. `issue` mutates the origin and the global log. `deliver` applies
    an issued remote event when the vector-clock precondition permits it. -/
inductive Step : System -> System -> Prop where
  | issue {sys : System} {id : ReplicaId} {kind : MutationKind} {atom : Atom}
      (hInRange : id < sys.replicaCount) :
      Step sys (issue sys id kind atom)
  | deliver {sys : System} {id : ReplicaId} {event : MutationEvent}
      (hInRange : id < sys.replicaCount)
      (hRemote : event.origin ≠ id)
      (hIssued : event ∈ sys.log)
      (hCausal : causallyDeliverable event (replicaAt sys id))
      (hPending : Not (hasApplied id event sys)) :
      Step sys (deliver sys id event)

/-- Reflexive transitive closure of `Step`. Kept local so the executable DAS module does not depend
    on Mathlib's relation library. -/
inductive StepStar : System -> System -> Prop where
  | refl (sys : System) : StepStar sys sys
  | trans {sys sys' sys'' : System} :
      Step sys sys' -> StepStar sys' sys'' -> StepStar sys sys''

theorem stepStarOne {sys sys' : System} (h : Step sys sys') : StepStar sys sys' :=
  StepStar.trans h (StepStar.refl sys')

theorem stepStarTrans {sys1 sys2 sys3 : System}
    (h12 : StepStar sys1 sys2) (h23 : StepStar sys2 sys3) : StepStar sys1 sys3 := by
  induction h12 with
  | refl _ => exact h23
  | trans hstep htail ih => exact StepStar.trans hstep (ih h23)

theorem replicaAt_replicas_set_self (replicas : List Replica) (log : List MutationEvent)
    (id : ReplicaId) (replica : Replica) (hInRange : id < replicas.length) :
    replicaAt ({ replicas := replicas.set id replica, log := log } : System) id = replica := by
  unfold replicaAt System.replicaCount
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  simp [hInRange]

theorem stepPreservesReplicaCount {sys sys' : System} (h : Step sys sys') :
    sys'.replicaCount = sys.replicaCount := by
  cases h <;> simp [issue, deliver, System.replicaCount, List.length_set]

theorem stepStarPreservesReplicaCount {sys sys' : System} (h : StepStar sys sys') :
    sys'.replicaCount = sys.replicaCount := by
  induction h with
  | refl _ => rfl
  | trans hstep _ ih => exact Eq.trans ih (stepPreservesReplicaCount hstep)

/-- Replicas observe their own issued mutations immediately. -/
theorem readOwnWrites (sys : System) (id : ReplicaId) (kind : MutationKind) (atom : Atom)
    (hInRange : id < sys.replicaCount) :
    hasApplied id (issuedEvent sys id kind atom) (issue sys id kind atom) := by
  unfold hasApplied eventsAppliedAt issue
  have h : id < sys.replicas.length := by
    simpa [System.replicaCount] using hInRange
  rw [replicaAt_replicas_set_self _ _ _ _ h]
  simp

/-- Applying a step never removes an existing global-log event. -/
theorem logMonotoneStep {sys sys' : System} (hstep : Step sys sys') {event : MutationEvent}
    (hmem : event ∈ sys.log) : event ∈ sys'.log := by
  cases hstep with
  | issue =>
      simp [issue, hmem]
  | deliver =>
      simp [deliver, hmem]

theorem logMonotoneStar {sys sys' : System} (hstar : StepStar sys sys') {event : MutationEvent}
    (hmem : event ∈ sys.log) : event ∈ sys'.log := by
  induction hstar with
  | refl _ => exact hmem
  | trans hstep _ ih => exact ih (logMonotoneStep hstep hmem)

/-- A named fair-delivery assumption. It is a theorem parameter, so any use has to display the
    network assumption at the call site. -/
def FairDeliveryFrom (sys : System) : Prop :=
  forall event id,
    event ∈ sys.log ->
    id < sys.replicaCount ->
    ∃ sys', StepStar sys sys' /\ hasApplied id event sys'

theorem eventualDelivery {sys : System} (fair : FairDeliveryFrom sys) {id : ReplicaId}
    {event : MutationEvent} (hIssued : event ∈ sys.log) (hInRange : id < sys.replicaCount) :
    ∃ sys', StepStar sys sys' /\ hasApplied id event sys' :=
  fair event id hIssued hInRange

/-- A barrier step can be extended until any pre-existing log event is applied at the target replica,
    provided the post-barrier state satisfies the fair-delivery assumption. -/
theorem barrierExtensionViaEventualDelivery {sys sys' : System} {id : ReplicaId}
    {event : MutationEvent} (fair : FairDeliveryFrom sys')
    (hInRange : id < sys.replicaCount) (hSteps : StepStar sys sys')
    (hIssued : event ∈ sys.log) :
    ∃ sys'', StepStar sys' sys'' /\ hasApplied id event sys'' := by
  have hInRange' : id < sys'.replicaCount := by
    rw [stepStarPreservesReplicaCount hSteps]
    exact hInRange
  exact fair event id (logMonotoneStar hSteps hIssued) hInRange'

/-- An event appears before another event in an application-order log. -/
def AppearsBefore (e1 e2 : MutationEvent) (events : List MutationEvent) : Prop :=
  ∃ (pre mid suf : List MutationEvent),
    events = pre ++ [e1] ++ mid ++ [e2] ++ suf

theorem existsSplitOfMem {event : MutationEvent} :
    forall events : List MutationEvent,
      event ∈ events -> ∃ (pre suf : List MutationEvent), events = pre ++ [event] ++ suf
  | [], h => by cases h
  | x :: xs, h => by
      simp at h
      rcases h with h | h
      · subst x
        exact ⟨[], xs, by simp⟩
      · rcases existsSplitOfMem xs h with ⟨pre, suf, hs⟩
        exact ⟨x :: pre, suf, by simp [hs, List.append_assoc]⟩

/-- Positional causal-consistency core: if two distinct events are both in one replica's application
    log, one has a definite FIFO position before the other. The stronger hb-directional statement
    needs an additional step-star invariant and remains a refinement target. -/
theorem causalConsistencyPositional {events : List MutationEvent} {e1 e2 : MutationEvent}
    (h1 : e1 ∈ events) (h2 : e2 ∈ events) (hNe : e1 ≠ e2) :
    AppearsBefore e1 e2 events \/ AppearsBefore e2 e1 events := by
  induction events with
  | nil => cases h1
  | cons x xs ih =>
      simp at h1 h2
      rcases h1 with h1 | h1
      · subst x
        rcases h2 with h2 | h2
        · subst e2
          exact False.elim (hNe rfl)
        · rcases existsSplitOfMem xs h2 with ⟨mid, suf, hs⟩
          left
          unfold AppearsBefore
          exact ⟨[], mid, suf, by simp [hs, List.append_assoc]⟩
      · rcases h2 with h2 | h2
        · subst x
          rcases existsSplitOfMem xs h1 with ⟨mid, suf, hs⟩
          right
          unfold AppearsBefore
          exact ⟨[], mid, suf, by simp [hs, List.append_assoc]⟩
        · rcases ih h1 h2 with hbefore | hafter
          · left
            rcases hbefore with ⟨pre, mid, suf, hs⟩
            unfold AppearsBefore
            exact ⟨x :: pre, mid, suf, by simp [hs, List.append_assoc]⟩
          · right
            rcases hafter with ⟨pre, mid, suf, hs⟩
            unfold AppearsBefore
            exact ⟨x :: pre, mid, suf, by simp [hs, List.append_assoc]⟩

theorem causalConsistency {sys : System} {id : ReplicaId} {e1 e2 : MutationEvent}
    (h1 : hasApplied id e1 sys) (h2 : hasApplied id e2 sys)
    (_hhb : hbDAS sys.replicaCount e1 e2) (hNe : e1 ≠ e2) :
    AppearsBefore e1 e2 (eventsAppliedAt id sys) \/
      AppearsBefore e2 e1 (eventsAppliedAt id sys) :=
  causalConsistencyPositional h1 h2 hNe

/-- A constructive mid-flight divergence witness: in a two-replica system, an issued local event can
    be visible at its origin before it is delivered to the other replica. -/
theorem midFlightDivergence :
    ∃ sys event,
      sys.replicaCount = 2 /\
      hasApplied 0 event sys /\
      Not (hasApplied 1 event sys) := by
  let atom := Atom.sym ""
  let event : MutationEvent :=
    { kind := MutationKind.add, atom := atom, origin := 0, clock := vcIncAt (vcZero 2) 0 }
  let replica0 : Replica := { id := 0, sigma := [atom], clock := event.clock, applied := [event] }
  let replica1 : Replica := initialReplica 2 1
  let sys : System := { replicas := [replica0, replica1], log := [event] }
  refine ⟨sys, event, ?_, ?_, ?_⟩
  · rfl
  · simp [hasApplied, eventsAppliedAt, replicaAt, sys, replica0]
  · simp [hasApplied, eventsAppliedAt, replicaAt, sys, replica1, initialReplica]

/-- A system is quiescent when every issued event has been applied at every in-range replica. -/
def Quiescent (sys : System) : Prop :=
  forall event id, event ∈ sys.log -> id < sys.replicaCount -> hasApplied id event sys

/-- Quiescent convergence as per-event coverage, matching the mechanized theorem that does not need
    an unordered CRDT equality axiom. -/
theorem dasConvergence {sys : System} {i j : ReplicaId} (hQuiescent : Quiescent sys)
    (hi : i < sys.replicaCount) (hj : j < sys.replicaCount) {event : MutationEvent}
    (hIssued : event ∈ sys.log) :
    hasApplied i event sys /\ hasApplied j event sys :=
  ⟨hQuiescent event i hIssued hi, hQuiescent event j hIssued hj⟩

/-- Extra assumptions needed to upgrade per-event coverage into ordered observable atom-set equality.
    This is deliberately stronger than quiescence. It names the missing CRDT/order condition instead
    of assuming ordered-list commutativity. -/
structure OrderedReplayAssumptions (sys : System) (i j : ReplicaId) : Prop where
  quiescent : Quiescent sys
  sameAppliedOrder : eventsAppliedAt i sys = eventsAppliedAt j sys
  leftReplay : (replicaAt sys i).sigma = replayEvents (eventsAppliedAt i sys)
  rightReplay : (replicaAt sys j).sigma = replayEvents (eventsAppliedAt j sys)

/-- Full local atom-set equality is proved only from explicit ordered-replay assumptions. -/
theorem sigmaConvergence {sys : System} {i j : ReplicaId}
    (h : OrderedReplayAssumptions sys i j) :
    (replicaAt sys i).sigma = (replicaAt sys j).sigma := by
  rw [h.leftReplay, h.rightReplay, h.sameAppliedOrder]

/-- Matching results converge when the local atom sets converge. -/
theorem matchingConvergesOfSigmaEq {sys : System} {i j : ReplicaId} {pattern : Atom}
    (hSigma : (replicaAt sys i).sigma = (replicaAt sys j).sigma) :
    matchesAt sys i pattern = matchesAt sys j pattern := by
  simp [matchesAt, localSpaceAt, Space.query, hSigma]

/-- Converged matching behavior follows from the same explicit ordered-replay assumptions as sigma
    equality. -/
theorem convergedMatchingBehavior {sys : System} {i j : ReplicaId} {pattern : Atom}
    (h : OrderedReplayAssumptions sys i j) :
    matchesAt sys i pattern = matchesAt sys j pattern :=
  matchingConvergesOfSigmaEq (sigmaConvergence h)

end Distributed
end Metta
