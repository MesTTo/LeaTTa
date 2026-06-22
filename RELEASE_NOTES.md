# LeaTTa 1.0.2

LeaTTa 1.0.2 is a patch release for the checked MeTTaIL runtime line. The release adds the denotational
interface used by the rset, rho, path-key RSpace, cost-accounting, and knotted-topoi papers, rewrites the
README, and keeps the Cordial Miners runtime bridge in the public release path.

## Announcement

LeaTTa 1.0.2 makes the 1.0 line easier to check. The root README now starts with the commands to run
and the output to expect. Then it explains the MeTTaIL runtime, the Cordial Miners bridge, and what is
still missing.

The MeTTaIL layer now includes `MeTTaIL.Semantics.Denotational`, a checked interface for labelled
transition systems, simulations, bisimulations, denotational kernels, context congruence, the
`FullyAbstract` property, path-key RSpace matching, and costed transition systems. The book connects that
interface to the rset, rho-calculus, path-key RSpace, cost-accounting, and knotted-topoi manuscripts. The
release does not claim the knotted topos, the MeTTaIL-to-rho desugaring, or the final coalgebra
construction as completed Lean proofs.

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
- The book cites the rset, rho, path-key RSpace, cost-accounting, and knotted-topoi papers and separates
  the Lean interface from the proofs that still need to be written.
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

The `--mettail` file format covers `sort`, `term`, and base `rewrite` declarations over S-expression
terms. The format is the CLI path into the checked runtime, not the full BNFC MeTTaIL surface parser.
The AC matcher used by the Cordial Miners runtime bridge covers the linear
collection fragment needed by those rules: one fixed payload and one rest variable.

The denotational-semantics addition says what a future model has to prove: denotational equality is the
same as context bisimilarity. The path-key layer records prefix comparability and the two subspace COMM
branches. The costed layer records costed traces and proves they forget to ordinary behaviour traces. The
knotted topos, rho desugaring functor, trie store, cut distributive law, and cost endofunctor are still
not in Lean.
