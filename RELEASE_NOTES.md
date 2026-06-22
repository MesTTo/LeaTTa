# LeaTTa 1.0.5

LeaTTa 1.0.5 extends the red/black denotational track with a checked category of reflective
universes. The runnable MeTTaIL runtime and Cordial Miners bridge remain in scope, while the knotted
topos, the full MeTTaIL-to-rho operational correspondence, and language-specific observational
calibration remain open work.

## Announcement

LeaTTa 1.0.5 adds the next checked categorical surface for the MeTTaIL denotational line.

`MeTTaIL.Semantics.KnottedUniverse` now defines `ReflectiveUniverseHom`, the structure-preserving maps
between red/black reflective universes. A morphism carries red sets, red atoms, black sets, and black
atoms forward, and it must commute with quote, drop, and the colour-swap equivalences.

The file also packages reflective universes as a Mathlib category. `ReflectiveUniverse.category`
supplies identity morphisms, composition, and the category laws for those structure-preserving maps.
The new names are included in the axiom audit.

The root README and the Verso book now describe the reflective-universe category directly. The docs
still draw the line where the Lean code currently draws it: the project has checked interfaces and
kernels for the denotational route, but it does not yet construct the knotted topos, prove finality for
the real rho behaviour functor, or prove the full MeTTaIL-to-rho desugaring theorem.

The next step is still to carry the MeTTaIL and Cordial Miners bridge deeper while turning the rho,
RSpace, and knotted-universe interfaces into concrete correspondence and finality proofs.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` still runs a term through a small editable MeTTaIL
  dialect file.
- Cordial Miners remains hosted as a MeTTaIL runtime presentation with AC-aware state and inbox
  rewriting.
- `MeTTaIL.Semantics.RSet` adds finite red/black rsets, atom opacity, finite support, colour-swap
  equivalences, and extensional union laws.
- `MeTTaIL.Semantics.KnottedUniverse` now has a category of reflective universes, a category of
  coalgebras, and the calibration bridge from final behaviour to full abstraction.
- The release bundles include `examples/bool.mettail`, so the MeTTaIL runtime path can be tested
  without a Lean toolchain.

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
The AC matcher used by the Cordial Miners runtime bridge covers the linear collection fragment needed
by those rules: one fixed payload and one rest variable.

The rho and denotational additions say what the future model has to prove and check the pieces already
in reach. The release does not claim the knotted topos, the full MeTTaIL-to-rho desugaring theorem, the
trie store, the cut distributive law, the cost endofunctor, or a language-specific
observational-calibration theorem.
