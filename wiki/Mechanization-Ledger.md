<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Mechanization Ledger

This page records the checked proof surface in this repository. It is a map from claim to Lean
declaration, not a replacement for the Lean files. A row is "checked" only when the declaration is in a
build target and the target has been rebuilt.

## Current Build Targets

`LeaTTa` is the executable target. It imports the Mathlib-free kernel and runner.

`Metatheory` is the proof target for the kernel. It imports `MettaHyperonFull.Proofs`.

`Operational` is the proof target for the four-register operational semantics.

`Distributed` is the active distributed atomspace target. It imports
`MettaHyperonFull.Distributed`.

The distributed target is separate from Cordial Miners. Cordial Miners proves consensus and ordering
claims. The distributed atomspace target proves replica-local mutation and delivery claims.

## Kernel And Proof Surface

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| One interpreter step is deterministic. | Checked | `Metta.interpretStack1_deterministic` | Function equality over `interpretStack1`. |
| Fuel-bounded interpretation is deterministic. | Checked | `Metta.interpretFuel_deterministic` | Function equality over `interpretFuel`. |
| Full evaluation is deterministic as a function. | Checked | `Metta.mettaEval_deterministic` | MeTTa nondeterminism remains in the returned list. |
| The `done` accumulator preserves all non-`Empty` results. | Checked | `Metta.interpretFuel_done` | The theorem states the runtime `Empty` filter explicitly. |
| First-argument rule indexing is sound. | Checked | `Metta.matchAtoms_headKey`, `Metta.candidates_sound` | Applies to the indexed equality-rule candidate set. |
| First-argument rule indexing is complete. | Checked | `Metta.candidates_complete` | Completeness is for rules that can match under the same head regime. |
| The gradual type checker never rejects undeclared operators. | Checked | `Metta.typeMismatch_undeclared` | Undeclared operators are `%Undefined%` style dynamic calls. |
| Gradual type compatibility is reflexive and symmetric. | Checked | `Metta.Consistent.refl`, `Metta.Consistent.symm` | It is intentionally not transitive. |
| Gradual type compatibility is not transitive. | Checked | `Metta.Consistent.not_transitive` | `%Undefined%` and `Atom` are dynamic tops, not a preorder. |
| A reported `BadArgType` comes from the checker after arity has passed. | Checked | `Metta.mettaEval_badArgType` | The arity check is a separate precondition. |
| The actual type in a `BadArgType` report is real. | Checked | `Metta.typeCheckArgs_act_real` | The actual type is drawn from `getTypes`. |
| User-defined equality-rule rewriting preserves declared type. | Checked | `Metta.reduction_preserves_type` | Requires the rule itself to be type-preserving. |
| The deterministic fragment is confluent. | Checked | `Metta.detStep_confluent` | Applies to the single-successor fragment. |
| Kernel query behavior matches the operational query reduct set. | Checked | `Metta.kernel_query_eq_mops_query` | This is the query correspondence theorem. |

## Atomspace Mutation Laws

The list-backed `Space` now has named mutation laws for the basic visibility facts used by later
proofs.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Inserting a structurally reflexive atom makes it visible to `contains`. | Checked | `Metta.Space.insert_contains_self` | Grounded floats can break host equality reflexivity, so the theorem names the condition. |
| Removing the atom just inserted restores the previous multiset. | Checked | `Metta.Space.removeOne_insert_self` | The theorem uses the list-backed `removeOne` semantics. |
| Inserting `(: a ty)` makes `ty` visible in `typeAssignments a`. | Checked | `Metta.Space.typeAssignments_insert_visible` | Requires structural reflexivity of the subject atom. |
| Inserting `(= lhs rhs)` makes the rule visible in `equalityRules`. | Checked | `Metta.Space.equalityRules_insert_visible` | Plain list membership over the current space. |

The structural-reflexivity predicate is deliberate:

```lean
Metta.Atom.StructurallyReflexive a := Atom.beq a a = true
```

Symbols and variables satisfy it directly through `Metta.Atom.sym_structurallyReflexive` and
`Metta.Atom.var_structurallyReflexive`. Grounded host values need their own host-side law when the
carrier can contain values like NaN.

## Distributed Atomspace

`MettaHyperonFull.Distributed.DAS` is the active Lean model for the distributed atomspace slice. It is
not Cordial Miners and does not prove consensus. It models replica-local atoms, mutation events, vector
clocks, local issue, remote delivery, and the proof boundary around fairness and replay order.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Vector-clock order is reflexive. | Checked | `Metta.Distributed.vcLeRefl` | Component order over the configured replica count. |
| Vector-clock order is transitive. | Checked | `Metta.Distributed.vcLeTrans` | Component order over the configured replica count. |
| Mutual vector-clock order gives component equality. | Checked | `Metta.Distributed.vcLeAntisym` | Equality is componentwise over the configured replica count. |
| A replica reads its own issued mutation immediately. | Checked | `Metta.Distributed.readOwnWrites` | Requires the issuing replica to be in range. |
| A single issued event can be visible at its origin before remote delivery. | Checked | `Metta.Distributed.midFlightDivergence` | This is the no-global-snapshot witness. |
| Existing log events are preserved by later steps. | Checked | `Metta.Distributed.logMonotoneStep`, `Metta.Distributed.logMonotoneStar` | The global log is append-only. |
| Eventual delivery follows from an explicit fair-delivery assumption. | Checked | `Metta.Distributed.eventualDelivery` | `FairDeliveryFrom` is a theorem parameter, not an axiom. |
| A barrier state can be extended until a previous event reaches a target. | Checked | `Metta.Distributed.barrierExtensionViaEventualDelivery` | Requires fairness from the post-barrier state. |
| Applied events have a definite application-log order. | Checked | `Metta.Distributed.causalConsistency` | Current theorem is positional. Directional happens-before is a future refinement. |
| Quiescence gives per-event coverage at any two replicas. | Checked | `Metta.Distributed.dasConvergence` | This does not claim ordered atom-list equality. |
| Ordered local atom sets converge under ordered-replay assumptions. | Checked | `Metta.Distributed.sigmaConvergence` | Requires `OrderedReplayAssumptions`. |
| Matching results converge when the local atom sets converge. | Checked | `Metta.Distributed.convergedMatchingBehavior` | Follows from ordered replay, not from fairness alone. |

The important design point is that full atom-list equality is not derived from quiescence alone. Local
atom storage is a list, and list append is order-sensitive. The stronger equality theorem therefore
requires `OrderedReplayAssumptions`. A future unordered carrier could replace that with a proved
semilattice or canonical-log theorem.

## Open Proof Boundaries

Substitution cyclicity needs a named audit. The current substitution file proves identity,
closed-atom stability, size monotonicity, lookup append, and composition. It should also record whether
any fuel-stability statement exists, and if so whether it requires acyclicity, closed codomains, or an
occurs-check invariant.

Grounded host laws need a named interface. Concrete builtins can be proved directly, but external
native callbacks should sit behind a small contract for equality, typing, matching, execution, and
observation.

The observation bridge should be named at theorem level. The executable already has observed
sequential evaluation, but the proof layer should expose the tuple that public checks compare:
directive input, returned atoms, error mode, world delta where modeled, and fuel status.

The query correspondence theorem should also be presented in four obligations: initial agreement, step
matching, observation compatibility, and termination preservation. The existing theorem is the proof
substance. The missing work is a small presentation layer that lets readers see which obligation is
covered by which declaration.

Type synthesis uniqueness modulo permutation is still open. `getTypes` totality is checked, but a
separate theorem should say when multiple type derivations are the same set up to ordering.

Named-space and state-cell mutation laws are still open at theorem level. The executable world state
models them. The proof layer should add small visibility theorems analogous to the new list-backed
`Space` laws.

## Verification Commands

The current focused checks are:

```bash
lake build Distributed
lake build Metatheory
```

`Distributed` also prints the axiom surface through `MettaHyperonFull.Distributed.AxiomAudit`.
