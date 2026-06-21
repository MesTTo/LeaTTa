# LeaTTa 1.0.1

LeaTTa 1.0.1 adds the checked MeTTaIL runtime path and the Cordial Miners runtime bridge to the public
release line.

## Announcement

This release adds the verified MeTTaIL runtime path. An editable language definition in the checked
LeaTTa MeTTaIL runtime format can be parsed, monomorphized, and run through the verified reducer. Each
executable step is tied back to the presentation semantics.

It also adds the PoR-weighted Cordial Miners formalization and runtime bridge. The coarse protocol is
encoded as real `MeTTaIL.AST`, run as a MeTTaIL presentation with AC-aware state and inbox rewriting,
and connected to the protocol model through simulation and stuttering-refinement theorems.

The next step will be deepening the bridge between MeTTaIL and Cordial Miners.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` runs a term through a small editable MeTTaIL dialect
  file.
- The release bundles include `examples/bool.mettail`, so the MeTTaIL runtime path can be tested
  without a Lean toolchain.
- Cordial Miners now has runtime demos for buried proposal events, ordered-prefix events, and finality.
- The book covers the MeTTa kernel, gradual type system, operational semantics, MeTTaIL runtime path,
  Cordial Miners safety core, proof status, and current limits.
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
lake build CordialMiners
./scripts/run-oracle.sh
./scripts/run-regression.sh
cd book && lake exe docs
```

## Scope

The `--mettail` file format is intentionally small: `sort`, `term`, and base `rewrite` declarations
over S-expression terms. It is the release-facing path into the checked runtime, not the full BNFC
MeTTaIL surface parser. The AC matcher used by the Cordial Miners runtime bridge covers the linear
collection fragment needed by those rules: one fixed payload and one rest variable.
