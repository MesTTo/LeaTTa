# LeaTTa 1.0.0

LeaTTa 1.0.0 is the first release that ships the MeTTaIL spec-to-runtime path in the `LeaTTa`
executable.

## Announcement

As quoted by Zarathustra Goertzel, "One of the MeTTa-IL style dreams is to be able to tweak the
LanguageDef specs for a MeTTa dialect and get a runtime for it." This is the realisation of it :))

The next step will be bridging MeTTaIL and Cordial Miners.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` runs a term through a small editable MeTTaIL
  dialect file.
- The release bundles include `examples/bool.mettail`, so the MeTTaIL runtime path can be tested
  without a Lean toolchain.
- The book covers the MeTTa kernel, gradual type system, operational semantics, MeTTaIL runtime path,
  Cordial Miners safety core, proof status, and current limits.
- The GitHub Pages workflow now builds API docs for the MeTTaIL and Cordial Miners libraries as well
  as the original kernel, metatheory, and operational-semantics targets.

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
./scripts/run-oracle.sh
./scripts/run-regression.sh
cd book && lake exe docs
```

## Scope

The `--mettail` file format is intentionally small: `sort`, `term`, and base `rewrite` declarations
over S-expression terms. It is the release-facing path into the checked runtime, not the full BNFC
MeTTaIL surface parser.
