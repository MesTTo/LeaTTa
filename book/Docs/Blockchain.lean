-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
LeaTTa: Chapter: MeTTa on the Blockchain.
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

#doc (Manual) "Paving the Way: MeTTa on the Blockchain" =>
%%%
tag := "sec-blockchain"
%%%

MeTTa is designed to run as an on-chain, smart-contract language. A contract runtime has three hard
requirements:

 * every validator must arrive at the same result from the same inputs;
 * gas must be metered in a way that cannot be cheated;
 * an optimised evaluator must stay faithful to the published semantics.

This chapter walks through the LeaTTa theorems that address those requirements.

# The Five Guarantees a Contract VM Needs

 * *Replayability*: every validator must agree. The machine is a Lean total *function*
   ({ref "sec-meta"}[determinism]); re-running on identical state returns an identical result list.
   Non-determinism is reified in that list, never hidden in the transition relation, so the set of
   outcomes is itself deterministic.
 * *Auditable state*: `smallStep?_kb_auditable` proves the knowledge base (the contract's persistent
   state) changes only via an explicit `add-atom`/`remove-atom`. No reduction step mutates state as a
   side effect.
 * *Sound gas metering*: `resourceStep?_energy_nonincreasing` proves total energy is monotonically
   non-increasing: a contract can spend gas but never mint it. Combined with a strictly-positive
   per-step cost, this gives bounded execution. Note: the per-step cost is present as an assumption;
   the development does not yet prove that all step costs are strictly positive (see the discussion
   chapter).
 * *No silent failure*: fuel exhaustion surfaces as MeTTa's `StackOverflow` error rather than a
   truncated result. An out-of-resources halt is distinguishable from a genuine answer.
 * *Optimisation-faithfulness*: `kernel_query_eq_mops_query` proves the indexed evaluator computes
   exactly the published specification's reduct set ({ref "sec-correspondence"}[the correspondence]).
   An implementation may index or cache without drifting from the spec.

# Type Safety as Contract Safety

On-chain, a type error must be caught deterministically and reported faithfully. The runtime must not
fabricate an error, and it must not reject a valid contract spuriously.

LeaTTa's gradual type-soundness results ({ref "sec-types"}[the type system]) give this property:
`BadArgType` is emitted exactly when the checker rejects an application, and the reported actual type is
a real type of the offending argument. The `%Undefined%`/`Atom` wildcards let contracts mix typed and
untyped code while keeping the typed parts checked soundly.

# Why a Machine-Checked Spec Matters Here

The MeTTa operational-semantics paper {citep mops}[] and the Hyperon whitepaper both call for an
independent specification comparable to the Ethereum Yellow Paper. Such a specification should be strong
enough to certify multiple implementations, and it should include a resource-bounded gas model for the
chain setting.

LeaTTa is a step toward that document being machine-checked. The spec (MOPS), the running interpreter,
and their correspondence live in one Lean development with no `sorry`, re-checked on every build.
