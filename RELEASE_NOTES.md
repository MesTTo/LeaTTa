# LeaTTa 1.0.2

LeaTTa 1.0.2 is a follow-up release for the checked MeTTaIL runtime line. The release adds a
source-backed denotational-semantics interface, rewrites the release-facing README, and keeps the
Cordial Miners runtime bridge in the public release path.

## Announcement

LeaTTa 1.0.2 tightens the 1.0 line around exact claims and testable entry points. The root README now
opens with the main validation commands and expected results, then explains the MeTTaIL runtime,
Cordial Miners bridge, and current open surface without alpha or work-in-progress framing.

The MeTTaIL layer now includes `MeTTaIL.Semantics.Denotational`, a checked interface for labelled
transition systems, simulations, bisimulations, denotational kernels, context congruence, and the
`FullyAbstract` property. The book connects that interface to the rset, rho-calculus, and knotted-topoi
manuscripts. The release does not claim the knotted topos, the MeTTaIL-to-rho desugaring, or the final
coalgebra construction as completed Lean proofs.

The next step is deepening the bridge between MeTTaIL and Cordial Miners.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` still runs a term through a small editable MeTTaIL
  dialect file.
- The release bundles include `examples/bool.mettail`, so the MeTTaIL runtime path can be tested
  without a Lean toolchain.
- Cordial Miners remains hosted as a MeTTaIL runtime presentation with AC-aware state and inbox
  rewriting.
- The book cites the rset, rho, and knotted-topoi papers and states which denotational claims are
  interfaces versus completed proofs.
- The GitHub Pages workflow builds the Verso book and API docs for the kernel, metatheory, operational
  semantics, MeTTaIL, MeTTaILProofs, and CordialMiners targets.

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

The `--mettail` file format is intentionally small: `sort`, `term`, and base `rewrite` declarations
over S-expression terms. The format is the release-facing path into the checked runtime, not the full BNFC
MeTTaIL surface parser. The AC matcher used by the Cordial Miners runtime bridge covers the linear
collection fragment needed by those rules: one fixed payload and one rest variable.

The denotational-semantics addition is an interface and theorem scaffold. The interface states the Lean
shape of full abstraction for a context-labelled system. The interface does not construct the knotted
topos or prove the rho desugaring functor.
