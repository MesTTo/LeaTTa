# Contributing

Thanks for looking at this. A note up front, because contribution here works a little differently
from most projects.

This repository does not define MeTTa. It formalizes it. The semantics belong to the MeTTa and
Hyperon developers, and this project follows what they decide. The whole point is to be a faithful,
machine-checked reference for the language they are building, validated against their own test
corpus, so a change that alters what the semantics actually are is not really ours to make. It has to
track a decision made upstream.

Because of that, I am honestly not sure yet what the long-term contribution model should look like.
For now the rule of thumb is this:

- Anything that changes the semantics, the type system, the operational model, or the proofs about
  them should come from the core MeTTa developers, or follow a decision they have already made. That
  is where the authority over the language lives, and this project should not get ahead of it.
- Obvious bug fixes are welcome from anyone. By that I mean a build that breaks, a proof that does not
  go through, a typo, a documentation error, or a place where the interpreter disagrees with
  Hyperon's own test corpus. Those are not semantic decisions, they are just correctness, and fixing
  them keeps the reference honest.

If you are not sure which of those two your change is, open an issue first and ask.

## House rules

A few invariants this project keeps, so any change has to keep them too:

- No `sorry`, no `admit`, no `native_decide`, no `partial`, and no `unsafe`. The whole thing is meant
  to be fully checked.
- The oracle stays green. `./scripts/run-oracle.sh` runs Hyperon's unmodified corpus and must report
  270 / 270, and `./scripts/run-regression.sh` covers the added-feature tests and must stay at PASS.
- Comments and docs are written in plain, measured prose, with no em dashes.
- The executable kernel (`Core`, `Minimal`, `Runtime`) stays free of Mathlib so that it remains
  runnable. Mathlib is only for the `Proofs` and `Operational` layers.

## Building and checking

```bash
lake build                   # kernel, the metta_full executable, and the Mathlib metatheory
./scripts/run-oracle.sh      # differential oracle against Hyperon's corpus, 270 / 270
./scripts/run-regression.sh  # the added-feature regression tests
```

If all three are green and the invariants above still hold, a bug-fix change is in good shape.

## The exploratory archive

The `archive/` directory holds earlier exploratory models. They are not built and are not part of the
faithful core, so please do not base contributions on them.
