# LeaTTa 1.0.3

LeaTTa 1.0.3 extends the checked MeTTaIL runtime and denotational track. It keeps the
1.0 release scope honest: the runnable runtime is real, the Cordial Miners bridge is in
the checked runtime path, and the knotted-topoi work is represented by checked interfaces
and small kernels, not by a claimed finished topos construction.

## Announcement

LeaTTa 1.0.3 adds three pieces to the MeTTaIL line.

The rho bridge now has a clearer K-machine staging path. The release includes candidate-ID
gating, ordinary and persistent K steps, K cell creation, named match-readiness helpers, and
a packet-level theorem that ties a successful MeTTaIL base rewrite to a ready K communication
step and the corresponding rho listener emission.

The denotational side now has the first checked red/black and store-facing surfaces. The
new `MeTTaIL.Semantics.KnottedUniverse` module records the four visible red/black sorts,
quote/drop round trips, a generic final-coalgebra interface, and the bridge from final
behaviour models to the existing `FullyAbstractModel`. The new
`MeTTaIL.Semantics.InteractingTrieMap` module records the reflective `RITM` equation from
the ITM sketch and connects Jetta-style packed binding addresses to the path-key RSpace
prefix relation.

The full-abstraction interface now names the last calibration step explicitly.
`BisimilarityCalibration` states when the chosen context-labelled bisimilarity agrees with an
object language's observational equivalence, and
`fullyAbstract_of_observation_calibration` turns the internal theorem into the user-facing
observational theorem.

The next step is still bridging MeTTaIL and Cordial Miners more deeply, while carrying the rho
and knotted-universe work from interfaces into concrete operational correspondence and finality
proofs.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` still runs a term through a small editable
  MeTTaIL dialect file.
- Cordial Miners remains hosted as a MeTTaIL runtime presentation with AC-aware state and inbox
  rewriting.
- The release bundles include `examples/bool.mettail`, so the MeTTaIL runtime path can be tested
  without a Lean toolchain.
- The book and README now describe the rho K bridge, the knotted-universe interface, the ITM and
  Jetta store sources, and the observational-calibration theorem.
- The GitHub Pages workflow builds the Verso book and API docs for the kernel, metatheory,
  operational semantics, MeTTaIL, MeTTaILProofs, and CordialMiners targets.

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
lake build MeTTaIL MeTTaILProofs MeTTaILTests
lake build CordialMiners CordialMiners.Runtime.Run
./scripts/run-oracle.sh
./scripts/run-regression.sh
cd book && lake exe docs
```

## Scope

The `--mettail` file format covers `sort`, `term`, and base `rewrite` declarations over
S-expression terms. The format is the CLI path into the checked runtime, not the full BNFC
MeTTaIL surface parser. The AC matcher used by the Cordial Miners runtime bridge covers the
linear collection fragment needed by those rules: one fixed payload and one rest variable.

The rho and denotational additions say what the future model has to prove and check the small
pieces already in reach. The release does not claim the knotted topos, the full MeTTaIL-to-rho
desugaring theorem, the trie store, the cut distributive law, the cost endofunctor, or a
language-specific observational-calibration theorem.
