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

MeTTa is intended to run as an on-chain, smart-contract language. A contract language places
unusually strict demands on its definition: every participant must compute the *same* result from
the same inputs, gas must be metered soundly, and an optimised production evaluator must be provably
faithful to the published semantics. LeaTTa's theorems were chosen to discharge exactly these
demands, and this chapter collects them into the case for MeTTa-on-chain.

# The Five Guarantees a Contract VM Needs

 * *Replayability*: every validator must agree. LeaTTa's machine is a Lean total *function*
   ({ref "sec-meta"}[determinism]); re-running a contract on identical state yields an identical
   result list. Non-determinism is reified in that list, never hidden in the transition relation, so
   "the set of outcomes" is itself a deterministic, replayable artifact.
 * *Auditable state*: `smallStep?_kb_auditable` proves the knowledge base (the contract's persistent
   state) changes *only* via an explicit `add-atom`/`remove-atom`. No reduction step can mutate state
   as a silent side effect, so every state transition is an attributable, authorised operation.
 * *Sound gas metering*: `resourceStep?_energy_nonincreasing` proves total energy is monotonically
   non-increasing: a contract can spend gas but never mint it. Combined with a strictly-positive
   per-step cost (the ingredients are in place), this yields bounded execution.
 * *No silent failure*: fuel exhaustion surfaces as MeTTa's `StackOverflow` error rather than a
   truncated result. An out-of-resources halt is therefore distinguishable from a genuine answer,
   which is essential when validators must agree not just on results but on *failure*.
 * *Optimisation-faithfulness*: `kernel_query_eq_mops_query` proves the indexed on-chain evaluator
   computes exactly the published specification's reduct set ({ref "sec-correspondence"}[the
   correspondence]). An implementation may optimise (index, cache) without drifting from the spec
   the network agreed on.

# Type Safety as Contract Safety

On-chain, a type error is a class of bug that must be caught deterministically and reported
faithfully, never fabricated, and never spuriously rejecting a valid contract. LeaTTa's gradual
type-soundness results ({ref "sec-types"}[the type system]) give precisely this: a `BadArgType` is
emitted *iff* the checker genuinely rejects an application, and the reported actual type is a real
type of the offending argument. The gradual `%Undefined%`/`Atom` discipline lets contracts mix typed
and untyped code without losing the guarantee that the *typed* parts are checked soundly.

# Why a Machine-Checked Spec Matters Here

The MeTTa operational-semantics paper {citep mops}[] and the Hyperon whitepaper both call for an
independent specification, a document of record comparable to the Ethereum Yellow Paper, against
which multiple implementations can be certified, with a resource-bounded (gas) model for the chain
setting.
LeaTTa is a step toward that document being not merely written but *machine-checked*: the spec (MOPS),
the running interpreter, and their correspondence all live in one Lean development with no `sorry`,
re-checked on every build. For a system whose bugs are economically exploitable, "the specification
type-checks, and the implementation provably matches it" is the right foundation.
