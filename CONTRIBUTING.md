# Contributing

A note up front, because contribution here works a little differently from most projects.

This repository does not define MeTTa. It formalizes it. The semantics belong to the MeTTa and
Hyperon developers, and this project follows what they decide. The aim is to be a machine-checked
reference for the language they are building, validated against their own test corpus. A change that
alters what the semantics actually are is not ours to make. It has to track a decision made upstream.

I am not sure yet what the long-term contribution model should look like. For now:

- Anything that changes the semantics, the type system, the operational model, or the proofs about
  them should come from the core MeTTa developers, or follow a decision they have already made. That
  is where the authority over the language lives, and this project should not get ahead of it.
- Bug fixes are welcome from anyone. That means a build that breaks, a proof that does not go through,
  a typo, a documentation error, or a place where the interpreter disagrees with Hyperon's own test
  corpus. Those are not semantic decisions and fixing them keeps the reference correct.

If you are not sure which of those two your change is, open an issue first and ask.

## House rules

Invariants the project keeps. Any change must keep them too:

- No `sorry`, no `admit`, no `native_decide`, no `partial`, and no `unsafe`. Everything must be
  fully checked.
- The oracle stays green. `./scripts/run-oracle.sh` runs Hyperon's unmodified corpus and must report
  270 / 270. `./scripts/run-regression.sh` covers the added-feature tests and must stay at PASS.
- Comments and docs are written in plain prose, with no em dashes.
- The executable kernel (`Core`, `Minimal`, `Runtime`) stays free of Mathlib. Mathlib is only for
  the `Proofs` and `Operational` layers.

## Building and checking

```bash
lake build                   # kernel, the LeaTTa executable, and the Mathlib metatheory
./scripts/run-oracle.sh      # differential oracle against Hyperon's corpus, 270 / 270
./scripts/run-regression.sh  # the added-feature regression tests
```

If all three are green and the invariants above still hold, a bug-fix change is ready to propose.

## The exploratory archive

The `archive/` directory holds earlier exploratory models. They are not built and are not part of the
verified core. Do not base contributions on them.
