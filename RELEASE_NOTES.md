<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# LeaTTa 1.0.7

LeaTTa 1.0.7 is the metatheory and distributed-atomspace release. It keeps the executable minimal
MeTTa interpreter aligned with Hyperon's oracle corpus, adds a checked distributed atomspace target,
and expands the public proof ledger for the kernel boundary.

## Announcement

The new `Distributed` target models the active distributed atomspace slice. It is separate from
Cordial Miners consensus. It covers replica-local atom storage, add/remove mutation events, vector
clocks, local issue, remote delivery, and the proof boundary around fairness and replay order.

The checked claims include vector-clock order laws, pairwise max as a least upper bound,
read-your-own-writes, mid-flight divergence before remote delivery, append-only global logs, fair
delivery as an explicit theorem parameter, barrier extension under that fairness parameter, quiescent
per-event coverage, ordered atom-set convergence under `OrderedReplayAssumptions`, and matching
convergence after ordered replay.

The kernel proof surface is also wider. The release adds executable binding merge laws, query
visibility laws, atomspace and threaded-world visibility laws, substitution-cycle audit facts,
theorem-facing observation records, host-law records for native grounded callbacks, arrow-constructor
laws, and a four-obligation packaging of the query correspondence theorem.

The release also keeps the runtime behavior aligned with the current Hyperon oracle expectations. The
minimal interpreter and standard library pass 270 assertions across 22 vendored corpus files, and the
added regression suite stays green.

## Highlights

- `MettaHyperonFull.Distributed` is now a public build target with an axiom audit.
- `MettaHyperonFull.Proofs.BindingLaws` records fresh, same-value, conflicting, and unifying binding
  merge cases.
- `MettaHyperonFull.Proofs.SpaceLaws` and `MettaHyperonFull.Proofs.WorldLaws` record insert, query,
  remove, type-assignment, equality-rule, named-space, state-cell, token, `&self`, and hidden-import
  visibility facts.
- `MettaHyperonFull.Core.QueryBackend` and `MettaHyperonFull.Proofs.QueryBackend` add a
  backend-neutral query interface, the list-backed reference backend, a generated reference backend for
  cache laws, and serial conjunctive-query laws.
- `MettaHyperonFull.Core.MorkCodec`, `MettaHyperonFull.Proofs.MorkCodec`,
  `MettaHyperonFull.Core.MorkEncodedSpace`, and `MettaHyperonFull.Proofs.MorkEncodedSpace` add a
  logical MORK codec model, decode-after-encode, repeated-variable coreference, decoded-space query
  refinement, and encoded-backend conjunctive-query laws.
- `MettaHyperonFull.Core.MorkNamespace` and `MettaHyperonFull.Proofs.MorkNamespace` add the MORK
  query-result namespace split and prove query/data disjointness plus result-id separation.
- `MettaHyperonFull.Core.MorkPrepared`, `MettaHyperonFull.Proofs.MorkPrepared`,
  `MettaHyperonFull.Core.MorkSharded`, and `MettaHyperonFull.Proofs.MorkSharded` add semantic
  snapshot, prepared-query, and finite-sharding equivalence laws.
- `MettaHyperonFull.Core.MorkNamedSpaces` and `MettaHyperonFull.Proofs.MorkNamedSpaces` add
  backend-level named-space visibility and isolation laws.
- `MettaHyperonFull.Core.MorkGroundedFilter`, `MettaHyperonFull.Proofs.MorkGroundedFilter`,
  `MettaHyperonFull.Core.MorkMM2`, and `MettaHyperonFull.Proofs.MorkMM2` add mutable-grounded
  live-value filtering laws and semantic MM2 exec readback laws.
- `MettaHyperonFull.Core.MorkCompactCodec` and `MettaHyperonFull.Proofs.MorkCompactCodec` refine the
  logical codec to compact `newVar`/`varRef` traces and prove compact decode-after-encode.
- `MettaHyperonFull.Core.MorkDecodedBindings` and `MettaHyperonFull.Proofs.MorkDecodedBindings` keep
  decoded MORK query-result variables structured through binding rows and prove query/data separation.
- `MettaHyperonFull.Core.MorkGroundedRegistry` and `MettaHyperonFull.Proofs.MorkGroundedRegistry`
  connect mutable-grounded live filters to stable host handles through a pure registry boundary.
- `MettaHyperonFull.Core.MorkMM2Lowering` and `MettaHyperonFull.Proofs.MorkMM2Lowering` add the
  MM2 lowering view for `I`/`,` source lists, `O`/`,` template lists, equality and inequality source
  constraints, add/remove effects, and priority-ordered semantic exec selection.
- `MettaHyperonFull.Core.MorkMM2Resources` and `MettaHyperonFull.Proofs.MorkMM2Resources` add a pure
  ACT resource boundary for lowered MM2 plans. ACT sinks write instantiated payloads to named resource
  spaces, ACT sources read those spaces, and resource names stay isolated from the main reference
  `Space`.
- `MettaHyperonFull.Proofs.SubstitutionAudit` records the boundary around cyclic bindings and
  fuel-bounded recursive resolution.
- `MettaHyperonFull.Minimal.Observation` records input, fuel, result atoms, error atoms, exhaustion,
  and before/after world state for one observed query.
- `MettaHyperonFull.Core.HostLaws` makes native carrier and grounded-function assumptions explicit.
- `MettaHyperonFull.Proofs.TypeConstructors` pins `Atom.mkArrow` and `TypeEnv.arrowParts?` to the
  executable arrow representation.
- The wiki source now includes a mechanization ledger and an axiom catalog for the checked public
  theorem surface.

## Quick Checks

From a release bundle:

```bash
bin/LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'
bin/LeaTTa --mettail examples/bool.mettail --term '(notOp tt)'
bin/LeaTTa --oracle examples/a1_symbols.metta
```

Expected outputs:

```text
[13]
ff
==== PASS=7  FAIL=0  TOTAL=7 ====
```

From a source checkout:

```bash
lake build
lake build Distributed Metatheory Operational
lake build MeTTaIL MeTTaILProofs MeTTaILTests
lake build CordialMiners CordialMiners.Runtime.Run
./scripts/run-oracle.sh
./scripts/run-regression.sh
cd book && lake exe docs
```

## Scope

The distributed atomspace target proves replica-local mutation and delivery claims. It does not prove
Cordial Miners consensus, and it does not derive ordered atom-list equality from quiescence alone.
List-backed atom storage is order-sensitive, so the equality and matching-convergence theorems require
explicit ordered-replay assumptions.

The release still does not claim the full Hyperon module system, MeTTa on Rholang, the knotted topos,
the full MeTTaIL-to-rho desugaring theorem, the trie store, the cut distributive law, the cost
endofunctor, or a language-specific observational-calibration theorem.
