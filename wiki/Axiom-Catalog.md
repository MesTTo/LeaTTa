<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Axiom Catalog

This page names the assumption surface for the checked Lean development. It is human-readable
documentation for the build-visible audit files. The audit files remain the source of truth.

The goal is simple: no orphan assumptions. If a theorem needs a network, host, ordering, or classical
logic boundary, that boundary should be visible in the theorem statement or in the audit output.

## Audit Files

| Area | Audit file | What it checks |
| --- | --- | --- |
| Distributed atomspace | `MettaHyperonFull/Distributed/AxiomAudit.lean` | The active DAS theorem surface. |
| MeTTaIL proofs | `MeTTaILProofs/AxiomAudit.lean` | The MeTTaIL proof surface. |
| Cordial Miners | `CordialMiners/AxiomAudit.lean` | Consensus theorem surface. |
| Cordial Miners runtime bridge | `CordialMiners/Runtime/AxiomAudit.lean` | Runtime bridge theorem surface. |

## Distributed Atomspace

`MettaHyperonFull.Distributed.DAS` introduces no project-level Lean axioms. Network fairness and
ordered replay are ordinary theorem parameters.

| Boundary | Lean name | Consumer | Status |
| --- | --- | --- | --- |
| Standard Lean proof irrelevance and classical reasoning | `propext`, `Classical.choice`, `Quot.sound` as reported by `#print axioms` | Some DAS theorems through list, equality, and quotient-backed library paths | Accepted Lean/Mathlib baseline. |
| Fair delivery from a state | `Metta.Distributed.FairDeliveryFrom` | `eventualDelivery`, `barrierExtensionViaEventualDelivery` | Explicit theorem parameter. |
| Quiescent per-event coverage | `Metta.Distributed.Quiescent` | `dasConvergence` | Explicit theorem parameter. |
| Ordered replay of applied logs into local atom storage | `Metta.Distributed.OrderedReplayAssumptions` | `sigmaConvergence`, `convergedMatchingBehavior` | Explicit theorem parameter. |

The audit target is:

```bash
lake build Distributed
```

The expected project-level result is that the audit reports only standard Lean and Mathlib axioms, and
no project-specific distributed-system axiom.

## Host And Grounded Values

The current executable kernel has concrete grounded values and concrete builtins. It also permits
external grounded payloads. That creates a real proof boundary.

The current checked laws include `Atom.StructurallyReflexive` for atom equality reflexivity where
space membership proofs require it, and `Atom.MatchReflexive` where `Space.query` visibility depends
on the executable matcher. These predicates are intentionally not automatic for every grounded value,
because host values can include non-reflexive equality or matching cases.

The public interface is `Metta.NativeCarrier` with laws in `Metta.NativeCarrierLaws`. It covers:

| Law | Reason |
| --- | --- |
| Grounded equality is reflexive on the values accepted by a theorem. | Needed for visibility and identity laws. |
| Grounded equality is symmetric and transitive where it is used as equality. | Needed before treating equality as an equivalence relation. |
| Grounded type is stable under the relevant builtin. | Needed for grounded preservation theorems. |
| Grounded matching is sound with respect to equality or the chosen matcher relation. | Needed before callback matching can feed theorem-level matching claims. |
| Native execution returns observations in the documented shape. | Needed before external execution can be used in observed behavior claims. |

Concrete builtins should prove these laws directly. External native callbacks should pass the contract
as an explicit theorem parameter.

Current consumers are:

| Consumer | Law field |
| --- | --- |
| `Metta.NativeCarrierLaws.typeOf_sound` | `type_sound` |
| `Metta.NativeCarrierLaws.matchWith_sound` | `match_sound` |
| `Metta.NativeCarrierLaws.executeSound` | `execute_sound` |
| `Metta.NativeCarrierLaws.displaySound` | `display_sound` |
| `Metta.GroundingLaws.impl_sound` | `execution_sound` |
| `Metta.GroundingLaws.typeSig_sound_of_some` | `typeSig_sound` |

## Substitution And Cycles

The active substitution theorems are ordinary Lean theorems, not axioms. The open issue is not axiom
use. The issue is theorem shape.

The proof layer should avoid any unconditional claim that a fuel-bounded substitution expansion is
stable across higher fuel when the substitution can contain cycles. If a future theorem needs such a
claim, it should require one of these conditions:

| Condition | Meaning |
| --- | --- |
| Acyclic substitution graph | Following variable links must terminate. |
| Closed codomain | Substitution values contain no variables that can be expanded again. |
| Occurs-check invariant | No binding places a variable under a term that can later expand back to it. |
| Decreasing measure | Every expansion step reduces a named well-founded measure. |

Current checked audit facts are:

| Consumer | What it proves |
| --- | --- |
| `Metta.cyclicSubst_apply_x_once` | One-pass substitution follows only one edge of a two-variable cycle. |
| `Metta.cyclicSubst_apply_x_twice` | Repeated application can change the result again. |
| `Metta.cyclicBindingsXY_not_direct_loop` | The direct-loop filter does not reject a longer cycle. |
| `Metta.cyclicResolve_not_fuel_stable` | Recursive resolution is not fuel-stable on cyclic bindings. |

## Observation Boundary

Observed behavior claims should not depend on hidden runtime choices. The proof layer should expose a
record or named tuple for:

| Field | Meaning |
| --- | --- |
| Input | The directive or top-level program fragment. |
| Results | Returned atoms after the same filtering rule as the executable. |
| Error mode | Error atom, stack overflow, bad type, bad arity, or no error. |
| World delta | Named-space, state-cell, token, or import delta where modeled. |
| Fuel status | Whether the result is complete or fuel-exhausted. |

The checked bridge is `Metta.Minimal.DirectiveObservation`. Its current consumers are:

| Consumer | What it proves |
| --- | --- |
| `Metta.Minimal.observeQuery_results` | Results are exactly the atom projection of `mettaEval`. |
| `Metta.Minimal.observeQuery_errors` | Error atoms are exactly `results.filter Atom.isError`. |
| `Metta.Minimal.observeQuery_worldBefore` | The observation records the input world. |
| `Metta.Minimal.observeQuery_worldAfter` | The observation records the evaluator's output world. |
