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

## Binding Merge Laws

The executable matcher merges `Bindings` through `Bindings.addVarBinding`, `Bindings.addVarEquality`,
and `Bindings.merge`. The checked laws mirror the useful single-step merge cases while preserving the
runtime's unification behavior.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Looking up a value in the empty binding set fails. | Checked | `Metta.Bindings.lookupVal_empty` | Direct value lookup only; equality aliases are not followed. |
| Raw value insertion makes the inserted value visible. | Checked | `Metta.Bindings.lookupVal_addValRaw_self` | `addValRaw` removes prior direct values for the variable. |
| A fresh direct value binding extends the binding set. | Checked | `Metta.Bindings.addVarBinding_fresh`, `Metta.Bindings.merge_one_val_fresh` | Fresh means `lookupVal b x = none`. |
| Re-adding the same structurally reflexive value keeps the binding set. | Checked | `Metta.Bindings.addVarBinding_same`, `Metta.Bindings.merge_one_val_same` | Grounded values need the same equality reflexivity condition used elsewhere. |
| A direct value conflict fails when old and new values are neither equal nor unifiable. | Checked | `Metta.Bindings.addVarBinding_conflict`, `Metta.Bindings.merge_one_val_conflict` | The unification-failure condition is explicit. |
| Distinct direct values can still merge when unification succeeds. | Checked | `Metta.Bindings.addVarBinding_unifies`, `Metta.Bindings.merge_one_val_unifies` | This is why the conflict law cannot be stated from inequality alone. |
| Equality aliases accept equal structurally reflexive values and reject unequal direct values. | Checked | `Metta.Bindings.addVarEquality_same`, `Metta.Bindings.addVarEquality_conflict` | Alias closure beyond one direct step is not claimed here. |
| Merging an empty right-hand binding set returns the original binding set as the only candidate. | Checked | `Metta.Bindings.merge_empty_right` | Exact executable `foldl` behavior. |

## Atomspace Mutation Laws

The list-backed `Space` now has named mutation laws for the basic visibility facts used by later
proofs.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Inserting a structurally reflexive atom makes it visible to `contains`. | Checked | `Metta.Space.insert_contains_self` | Grounded floats can break host equality reflexivity, so the theorem names the condition. |
| Inserting a matcher-reflexive atom makes it visible to `query` with the empty binding. | Checked | `Metta.Space.query_insert_self` | Uses the exact `matchAtoms a a` condition required by executable query. |
| Removing the atom just inserted restores the previous multiset. | Checked | `Metta.Space.removeOne_insert_self` | The theorem uses the list-backed `removeOne` semantics. |
| Querying after removing the atom just inserted matches the original space query. | Checked | `Metta.Space.query_removeOne_insert_self` | Query-facing consequence of exact single-copy removal. |
| Inserting `(: a ty)` makes `ty` visible in `typeAssignments a`. | Checked | `Metta.Space.typeAssignments_insert_visible` | Requires structural reflexivity of the subject atom. |
| Inserting `(= lhs rhs)` makes the rule visible in `equalityRules`. | Checked | `Metta.Space.equalityRules_insert_visible` | Plain list membership over the current space. |
| Updating a state cell makes the new value visible. | Checked | `Metta.World.setStore_visible` | Visibility through `World.store`. |
| Creating a named space makes it visible as an empty atom list. | Checked | `Metta.World.newSpace_visible` | Visibility through `World.spaces`. |
| Appending to a named space is visible at that name. | Checked | `Metta.World.appendSpace_visible` | Existing atoms are preserved and new atoms append. |
| Binding a token makes the value visible at that token name. | Checked | `Metta.World.bindTok_visible` | Visibility through `World.tokens`. |
| Appending to `&self` and hidden imports updates the corresponding world lists. | Checked | `Metta.World.appendSelf_visible`, `Metta.World.appendSelfImport_visible` | These are exact list equations. |
| Removing from `&self` uses the executable list erase behavior. | Checked | `Metta.World.eraseSelf_visible` | Duplicate-sensitive list behavior is stated directly. |

The structural-reflexivity predicate is deliberate:

```lean
Metta.Atom.StructurallyReflexive a := Atom.beq a a = true
```

Symbols and variables satisfy it directly through `Metta.Atom.sym_structurallyReflexive` and
`Metta.Atom.var_structurallyReflexive`. Grounded host values need their own host-side law when the
carrier can contain values like NaN.

Direct query visibility uses the matcher-facing predicate:

```lean
Metta.Atom.MatchReflexive a := [] ∈ matchAtoms a a
```

Symbols and variables satisfy it through `Metta.Atom.sym_matchReflexive` and
`Metta.Atom.var_matchReflexive`. Grounded and compound atoms can use the predicate directly when the
executable matcher proves self-matching for the value in question.

## Distributed Atomspace

`MettaHyperonFull.Distributed.DAS` is the active Lean model for the distributed atomspace slice. It is
not Cordial Miners and does not prove consensus. It models replica-local atoms, mutation events, vector
clocks, local issue, remote delivery, and the proof boundary around fairness and replay order.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Vector-clock order is reflexive. | Checked | `Metta.Distributed.vcLeRefl` | Component order over the configured replica count. |
| Vector-clock order is transitive. | Checked | `Metta.Distributed.vcLeTrans` | Component order over the configured replica count. |
| Mutual vector-clock order gives component equality. | Checked | `Metta.Distributed.vcLeAntisym` | Equality is componentwise over the configured replica count. |
| Pairwise vector-clock max reads componentwise. | Checked | `Metta.Distributed.vcGet_vcMax` | Missing components read as zero. |
| Pairwise vector-clock max is an upper bound. | Checked | `Metta.Distributed.vcLeMaxLeft`, `Metta.Distributed.vcLeMaxRight` | Component order over the configured replica count. |
| Pairwise vector-clock max is the least upper bound. | Checked | `Metta.Distributed.vcMaxLub` | Requires the candidate clock to bound both inputs. |
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

## Substitution And Binding Cycles

The substitution audit is now checked in `MettaHyperonFull.Proofs.SubstitutionAudit`.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| One-pass substitution does not recursively chase a two-variable cycle. | Checked | `Metta.cyclicSubst_apply_x_once`, `Metta.cyclicSubst_apply_x_twice` | The core `Subst.apply` has no fuel parameter. |
| The direct-loop filter catches self loops. | Checked | `Metta.directValueLoop_hasLoop`, `Metta.directAliasLoop_hasLoop` | It is a direct-loop check. |
| The direct-loop filter does not reject a length-two binding cycle. | Checked | `Metta.cyclicBindingsXY_not_direct_loop` | Longer cycles need a separate acyclicity invariant. |
| Recursive resolution is not fuel-stable on cyclic bindings. | Checked | `Metta.cyclicResolve_not_fuel_stable` | Any future fuel-stability theorem needs acyclicity, closed codomains, or a decreasing measure. |

## Host Laws

The host/native law interface is now checked in `MettaHyperonFull.Core.HostLaws`.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| Native carriers can expose equality, matching, type, execution, and display contracts. | Checked | `Metta.NativeCarrier`, `Metta.NativeCarrierLaws` | These records introduce no inhabitants or axioms. |
| Carrier type, matcher, executor, and display consumers use explicit law records. | Checked | `Metta.NativeCarrierLaws.typeOf_sound`, `Metta.NativeCarrierLaws.matchWith_sound`, `Metta.NativeCarrierLaws.executeSound`, `Metta.NativeCarrierLaws.displaySound` | External callbacks must pass the law record. |
| Individual grounded functions can expose implementation and type-signature laws. | Checked | `Metta.GroundingLaws`, `Metta.GroundingLaws.impl_sound`, `Metta.GroundingLaws.typeSig_sound_of_some` | Concrete builtin law instances can be added when needed. |

## Observation Bridge

The theorem-level observation bridge is now checked in `MettaHyperonFull.Minimal.Observation`.

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| One directive observation records input, fuel, results, errors, stack-overflow status, and world delta. | Checked | `Metta.Minimal.DirectiveObservation`, `Metta.Minimal.WorldDelta` | It wraps the existing evaluator. |
| Observed fuel is exactly the requested fuel budget. | Checked | `Metta.Minimal.observeQuery_fuel` | The bridge records the budget by value. |
| Observed results are exactly the atom projection of `mettaEval`. | Checked | `Metta.Minimal.observeQuery_results` | No new evaluator is introduced. |
| Observed errors are exactly `results.filter Atom.isError`. | Checked | `Metta.Minimal.observeQuery_errors` | Error classification follows `Atom.isError`. |
| Observed exhaustion is exactly stack-overflow detection over observed results. | Checked | `Metta.Minimal.observeQuery_exhausted` | Current executable signal for fuel exhaustion is the stack-overflow error atom. |
| Observed world before/after fields match the threaded state. | Checked | `Metta.Minimal.observeQuery_worldBefore`, `Metta.Minimal.observeQuery_worldAfter` | State deltas are recorded by value. |

## R.1 To R.4 Correspondence Presentation

The query correspondence theorem is now packaged as four obligations.

| Obligation | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| R.1 initial agreement. | Checked | `Metta.QueryCorrespondenceR14.initialAgreement` through `Metta.queryCorrespondenceR14` | Identity relation on atoms. |
| R.2 step matching. | Checked | `Metta.QueryCorrespondenceR14.stepMatching` through `Metta.queryCorrespondenceR14` | Same `KernelStep` and `MopsStep` scope as the base theorem. |
| R.3 observation compatibility. | Checked | `Metta.QueryCorrespondenceR14.observationCompatibility` through `Metta.queryCorrespondenceR14` | Reduct membership compatibility. |
| R.4 termination preservation. | Checked | `Metta.QueryCorrespondenceR14.terminationPreservation` through `Metta.queryCorrespondenceR14` | Empty reduct set compatibility. |

## Type Synthesis

| Claim | Status | Lean evidence | Boundary |
| --- | --- | --- | --- |
| `getTypes` is total. | Checked | `Metta.getTypes_ne_nil` | Every atom receives at least one type. |
| Computed type synthesis is unique modulo permutation. | Checked | `Metta.getTypes_unique_modulo_permutation` | This is the function-level theorem. A future relational synthesis judgment can strengthen it. |
| `Atom.mkArrow args ret` is recognized as an arrow type. | Checked | `Metta.Atom.isArrow_mkArrow` | Exact executable arrow constructor. |
| `TypeEnv.arrowParts?` recovers the arguments and return type from `Atom.mkArrow`. | Checked | `Metta.TypeEnv.arrowParts?_mkArrow` | Direct splitter law for `(-> A1 ... An R)`. |
| Non-arrow atoms and `(->)` without a return type do not split as arrow types. | Checked | `Metta.TypeEnv.arrowParts?_sym`, `Metta.TypeEnv.arrowParts?_var`, `Metta.TypeEnv.arrowParts?_gnd`, `Metta.TypeEnv.arrowParts?_empty_expr`, `Metta.TypeEnv.arrowParts?_arrow_no_return` | Negative cases for the executable splitter. |

## Verification Commands

The current focused checks are:

```bash
lake build Distributed
lake build Metatheory
```

`Distributed` also prints the axiom surface through `MettaHyperonFull.Distributed.AxiomAudit`.
