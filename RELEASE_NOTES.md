# LeaTTa 1.0.4

LeaTTa 1.0.4 is a focused metatheory release. It builds on the 1.0 runtime line by making the
red/black denotational track more explicit in Lean. The runnable MeTTaIL runtime and Cordial Miners
bridge remain in scope, while the knotted topos, the full MeTTaIL-to-rho operational correspondence,
and language-specific observational calibration remain open work.

## Announcement

LeaTTa 1.0.4 adds five checked pieces to the MeTTaIL denotational line.

The rset paper now has a finite Lean core. `MeTTaIL.Semantics.RSet` defines finite red and black sets,
atoms as sealed opposite-colour sets, finite support for atom renaming, colour-swap equivalences, and
an exact-member extensional quotient with finite union laws. Those union laws prove that empty is
neutral and that union is idempotent, commutative, and associative at the extensional level.

The rset core is tied back to the generic red/black interface. The `reflective_*` theorems identify
the `ReflectiveUniverse` quote/drop and colour-swap fields with the concrete rset functions. This keeps
the rset work connected to the knotted-universe surface instead of living as a separate model.

The coalgebra side now uses standard category-theory language. `CoalgebraHom` gives the morphisms
between coalgebras for a `TypeEndofunctor`, `Coalgebra.category` packages them as a Mathlib category,
and `FinalCoalgebra.isTerminal` states that a final coalgebra is a terminal object in that category.

The final-behaviour model now exposes the last calibration step directly.
`FinalBehaviourModel.fullyAbstractFor` calibrates final-behaviour equality against a chosen
object-language equivalence, and `FinalBehaviourModel.fullyAbstractForObservations` does the same for
an observation family. These theorems are axiom-free.

The README and Verso book now state the current scope more directly. The project has checked interfaces
and kernels for the denotational route. It does not yet construct the knotted topos, prove finality for
the real rho behaviour functor, or prove the full MeTTaIL-to-rho desugaring theorem.

The next step is still to carry the MeTTaIL and Cordial Miners bridge deeper while turning the rho and
knotted-universe interfaces into concrete correspondence and finality proofs.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` still runs a term through a small editable MeTTaIL
  dialect file.
- Cordial Miners remains hosted as a MeTTaIL runtime presentation with AC-aware state and inbox
  rewriting.
- `MeTTaIL.Semantics.RSet` adds finite red/black rsets, atom opacity, finite support, colour-swap
  equivalences, and extensional union laws.
- `MeTTaIL.Semantics.KnottedUniverse` now states final coalgebras as terminal objects in the category
  of coalgebras and links final-behaviour models to observational calibration.
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
