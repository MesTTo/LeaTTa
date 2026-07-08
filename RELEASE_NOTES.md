<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# LeaTTa 1.0.6

LeaTTa 1.0.6 adds the next checked piece of the generated-hypercube layer. Modal sites, spatial heads,
slot families, rule schemes, and judgment footprints were already represented in Lean. This release
adds explicit slot constraints and connects them to the finite equational-center checker.

## Announcement

LeaTTa 1.0.6 moves the generated-hypercube work one step closer to the center construction described
by Stay, Meredith, and Wells.

`MeTTaIL.Semantics.Hypercube` now defines `SlotConstraint`, the explicit equality that says two
generated slots must receive the same sort. The file also adds nullary slot expressions, so those
equalities can be seen by the generic equation checker already used for the hypercube center.

The new `constrainedCenter` and `Presentation.hypercubeConstrainedCenter` functions compute the center
under a list of explicit slot constraints. The theorem `mem_constrainedCenter_iff` states the exact
meaning of that computation: a member is a raw slot assignment that satisfies every listed slot
equality. The bridge theorems are included in the axiom audit and in the Verso theorem register.

The checked claim is precise. The release checks explicit slot constraints. It does not yet
derive every constraint automatically from source equations and rewrite laws, and it does not yet turn
the recorded judgment footprints into the full generated typing system. Those are the next hypercube
obligations.

## Highlights

- The minimal MeTTa interpreter and standard library still pass Hyperon's vendored oracle corpus:
  270 assertions across 22 files.
- `LeaTTa --mettail FILE --term TERM [--fuel N]` still runs a term through a small editable MeTTaIL
  dialect file.
- Cordial Miners remains hosted as a MeTTaIL runtime presentation with AC-aware state and inbox
  rewriting.
- `MeTTaIL.Semantics.Hypercube` now has checked explicit slot constraints, the constrained center, and
  the membership theorem connecting that center to direct constraint satisfaction.
- The denotational files still provide checked interfaces and small kernels for the rset, rho/RSpace,
  and knotted-universe route. They do not claim the knotted topos or full rho operational
  correspondence.
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

The hypercube layer now checks explicit slot constraints through the finite center machinery. The
automatic derivation of those constraints from source equations and rewrite laws remains open, as does
the full generated typing theorem for binder calculi.

The rho and denotational additions say what the future model has to prove and check the pieces already
in reach. The release does not claim the knotted topos, the full MeTTaIL-to-rho desugaring theorem, the
trie store, the cut distributive law, the cost endofunctor, or a language-specific
observational-calibration theorem.
