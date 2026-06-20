# MeTTa minimal interpreter: a machine-checked reference semantics in Lean 4

> **Alpha.** LeaTTa is an early, alpha-stage release and a starting foundation. It will be improved
> substantially in upcoming iterations as MeTTa is more fully formalised. It formalizes Hyperon
> Experimental's minimal interpreter and standard library, and now adds a first, still-incomplete
> formalization of MeTTa-IL, the MeTTa intermediate language, built from F1R3FLY's MeTTaIL repository
> (<https://github.com/F1R3FLY-io/MeTTaIL>). That MeTTa-IL layer is work in progress: it models the
> determinate core, cross-checks it against the real tool, and flags the parts that are still open (see
> the MeTTaIL section below). This release also adds a formalization of PoR-weighted Cordial Miners, a
> leaderless DAG consensus protocol, with a machine-checked end-to-end safety result (see the Cordial
> Miners section below). MeTTa on Rholang is still planned.

This is a Lean 4 formalization of Hyperon's minimal MeTTa interpreter, the small "assembly language"
that the rest of MeTTa is built on. The standard library is written in MeTTa on top of those
instructions, the same way `hyperon-experimental` does it. The kernel is total and has no
dependencies: no Mathlib, no Batteries.

The aim is simple. This should be a reference the Hyperon developers can actually use. It runs
Hyperon's own test files and agrees with them, every function is total (no `partial`, no `sorry`, no
`unsafe`), and wherever it differs from the current implementation, it differs by being cleaner. The
full comparison is in the book's Improvements over Hyperon appendix at
[mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## The faithful core

The kernel lives in `MettaHyperonFull/Minimal/`:

- `Interpreter.lean` is a faithful port of `interpreter.rs`. It is the continuation-passing,
  nondeterministic stack machine with all thirteen minimal instructions (`eval`/`evalc`, `chain`,
  `unify`, `cons-atom`/`decons-atom`, `function`/`return`, `collapse-bind`/`superpose-bind`, `metta`,
  `metta-thread`, `capture`, `context-space`). One step is a total function, and the driver is
  fuel-bounded with a termination measure that Lean checks. MeTTa can legitimately loop forever, so
  the bound is explicit rather than hidden.
- `Stdlib.lean` is the standard library, written as MeTTa over those thirteen instructions: `if`,
  `let`, `let*`, `switch`, `case`, `map-atom`, `filter-atom`, `foldl-atom`, the set operations, the
  `assert*` family, `match`, and so on, together with the grounded operations.

The whole library builds in 36 jobs, with 0 `sorry`, 0 `partial`, and 0 `unsafe`.

## How it is validated

The test is whether it agrees with Hyperon. It runs as a differential oracle against Hyperon's own
unmodified test corpus, vendored under [tests/corpus/](tests/corpus/) (MIT, commit `3f76dc4`). One
command builds the interpreter, runs every `!`-assertion in all 22 files, and checks each result. An
assertion passes when it evaluates to `()`. The script exits non-zero on any mismatch, so it doubles
as the regression gate.

```bash
./scripts/run-oracle.sh                                       # 270 / 270, ORACLE OK
lake exe LeaTTa --oracle tests/corpus/test_stdlib.metta   # or a single file
```

| Hyperon test file | result |
|---|---|
| `lib/tests/test_stdlib.metta` (the stdlib oracle) | 39 / 39 |
| `a1_symbols`, `a2_opencoggy`, `a3_twoside` (conjunctive `(, …)`) | 7 / 7, 1 / 1, 4 / 4 |
| `b0_chaining_prelim`, `b1_equal_chain`, `b2_backchain`, `b3_direct` | 5 / 5, 8 / 8, 6 / 6, 4 / 4 |
| `b4_nondeterm.metta` (`collapse`/`superpose` comma-tuples) | 11 / 11 |
| `b5_types_prelim.metta` (type system) | 26 / 26 |
| `c1_grounded_basic.metta`, `c3_pln_stv.metta` | 21 / 21, 5 / 5 |
| `c2_spaces.metta` (named spaces, `import!`, `fork-space`, MORK) | 25 / 25 |
| `e1_kb_write`, `e2_states`, `e3_match_states` (mutable spaces, state cells) | 3 / 3, 14 / 14, 9 / 9 |
| `d1_gadt.metta` (GADTs), `d2_higherfunc.metta` (higher-order functions) | 14 / 14, 25 / 25 |
| `d3_deptypes`, `d4_type_prop` (types as propositions), `d5_auto_types` | 8 / 8, 18 / 18, 7 / 7 |
| `g1_docs.metta` (`get-doc`, `help!`) | 10 / 10 |

These are Hyperon's tests, run unmodified. Passing tests include the full dependent-type tier
(`d1`–`d5`): GADTs, higher-order functions, dependent length arithmetic, types as propositions, and
auto type-checking, along with the documentation operators `get-doc` and `help!`.

One file is excluded: `f1_imports.metta`. Hyperon marks it Python-mode-only (its header says it
"won't work under no python mode"), because it assumes `&self` starts nearly empty with `corelib` and
`stdlib` as separate modules, while this build ships the prelude inside `&self`. The module machinery
it would exercise, `import!` into named spaces and diamond-dependency deduplication, is covered by
`c2_spaces` (25/25) and `g1_docs` (10/10).

## What is implemented

All of this is built on the minimal interpreter and follows Hyperon:

- Types: gradual `get-type`, function-application checking with `(BadArgType …)`, multi-type symbols,
  and type-variable unification for parametric and dependent signatures like `(-> $t $t …)` and
  `(List $a)`, plus mixed integer and float arithmetic.
- Spaces and state: named spaces (`new-space`, `add-atom`, `remove-atom`, `get-atoms`), `match` over
  `&self` and named spaces, conjunctive `(, …)` match, state cells (`new-state`, `get-state`,
  `change-state!`), `bind!` tokens, and `import!`, which is the only IO. Hyperon does this with
  `Rc<RefCell>` mutation; here it is a pure threaded `World` of named spaces, a state store, and token
  bindings, sequenced through evaluation.
- Sequential evaluation, so each `!`-query sees only the knowledge base before it, the way Hyperon
  reads a file. The cross-argument binding propagation that `(ift (green $x) $x)` needs is done with
  scope-based retention instead of mutation.

## The proofs

The metatheory layer lives in `MettaHyperonFull/Proofs/`. It uses Mathlib and keeps 0 `sorry`, 0
`admit`, and 0 `native_decide`. It proves what an on-chain MeTTa needs:

- the abstract machine is deterministic, with all nondeterminism kept in the result list rather than
  the transition relation, which is what replayability needs;
- its deterministic fragment is confluent;
- first-argument rule indexing is sound and complete, so it offers exactly the rules that can fire.
  This is the same-head case where Hyperon's `Space::visit` undercounts (issue #1079);
- the gradual type checker is total, and reports `BadArgType` faithfully and only with a real argument
  type, so it never invents an error;
- α-equivalence is an equivalence relation.

A separate `MettaHyperonFull.Operational.*` library machine-checks the published Meta-MeTTa
operational semantics (arXiv 2305.17218): the four-register machine ⟨i,k,w,o⟩, its barbed
bisimulation, and a resource-bounded (gas) extension. The bridge between the indexed kernel and that
specification is in `Proofs/Correspondence.lean`, covered in the book's operational-semantics and
correspondence chapters at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## MeTTaIL (work in progress)

`MeTTaIL/` is a first machine-checked formalization of F1R3FLY's MeTTaIL, the meta-language that turns a
presentation of a graph-structured lambda theory into a calculus's grammar, equations, and rewrites. It
is built from the F1R3FLY MeTTaIL repository (<https://github.com/F1R3FLY-io/MeTTaIL>) and it is not
finished. It models the determinate core and is honest about what is still open.

What is checked: the elaborate, desugar, type-lift, and monomorphize pipeline, pinned by kernel
`decide` against output captured from the real Scala tool on `Rholang.module`; the GSLT reduction
relation (soundness); subject reduction and confluence for SKI and the simply-typed lambda calculus;
the semantic cores of the two papers' calculi (the spice bounded-reachability rule and the mq-calculus
Born-rule probability conservation); the MeTTa-to-GSLT bridge; and the presentation lattice laws with
decidable equality. It builds with 0 `sorry`/`admit`/`native_decide`/`partial`/`unsafe`, and the axiom
audit shows only the three standard axioms.

What is open: the modal hypercube typing for binder calculi (open in the source itself), the
rho-calculus full-abstraction result, the spice and mq calculi as full reduction theories, a standalone
rho-calculus reduction development, the per-variable category-consistency check in the elaborator, and
an operational bisimulation against the four-register machine. These are flagged in the code and in
[`MeTTaIL/SPECIFICATION.md`](MeTTaIL/SPECIFICATION.md).

Formalizing the tool also turned up several bugs in it. They are written up for the F1R3FLY team in
[`MeTTaIL/HYPERON_IMPROVEMENTS.md`](MeTTaIL/HYPERON_IMPROVEMENTS.md). The full treatment is the MeTTaIL
chapter in the book at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/). Build it with the
rest of the proofs:

```bash
lake build MeTTaIL MeTTaILProofs MeTTaILTests
```

## Cordial Miners (PoR-weighted consensus)

`CordialMiners/` is a machine-checked formalization of PoR-weighted Cordial Miners, a leaderless
DAG-based BFT consensus protocol (arXiv 2205.09174), in the weighted Proof-of-Reputation variant from a
blueprint by Ben Goertzel. It is the consensus layer a MeTTa contract would run on a chain, and it is
held to the same bar: 0 `sorry`/`admit`/`native_decide`/`partial`/`unsafe`, with every headline theorem
axiom-clean (only the three standard axioms, never `sorryAx`).

The headline is end-to-end safety: under a Byzantine-weight bound, honest non-equivocation, and finality
permanence, the protocol never finalizes conflicting values and correct miners never publish conflicting
positions. The hard part, the ordering's prefix-monotonicity, is not assumed. It is derived in stages
down to those three named facts. The library spans the full pipeline: the weighted-overlap safety
keystone and threshold finality, the blocklace and equivocation detection, final-leader ratification, a
verified concrete topological-sort ordering (deterministic, complete, causally sound, no `partial`), a
coarse/fine refinement tied by a forward simulation, lossless extraction to MeTTa-IL atoms, an
executable end-to-end simulation, and the top-level safety aggregate. The overview is in
[`CordialMiners/README.md`](CordialMiners/README.md), and the full treatment is the Cordial Miners
chapter in the book.

```bash
lake build CordialMiners
```

## Documentation

The book and a generated API reference are published together at
[mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/):

- the book, a textbook-style treatment, at the site root;
- the API reference, every definition and theorem generated by doc-gen4, at
  [/api](https://mestto.github.io/LeaTTa/api/). References into Mathlib link to the official Mathlib
  documentation.

## The book

A textbook-style treatment of the formalization is in [`book/`](book/), built with Verso. It covers
the object language, the interpreter, the type system, the metatheory, the operational semantics and
its correspondence to the kernel, the blockchain angle, the MeTTaIL framework, and the Cordial Miners
consensus formalization. The book is its own Lean project, so build it separately:

```bash
cd book
lake exe docs                                               # builds the book
```

The generated site lands in `book/_out/html-multi/`. To read it, open that folder's `index.html` in a
browser, or serve it locally:

```bash
python3 -m http.server 8137 --directory book/_out/html-multi   # then open http://localhost:8137/
```

## Install and run

The interpreter ships as a single native binary, `LeaTTa`. It links only against the standard
C library, so a prebuilt release runs on any glibc Linux of the same architecture without installing
the Lean toolchain. Download an archive from the [releases page](https://github.com/MesTTo/LeaTTa/releases),
then:

```bash
tar xzf leatta-0.5.0-linux-x86_64.tar.gz
cd leatta-0.5.0-linux-x86_64 && ./install.sh   # installs to ~/.local/bin
LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'             # [13]
```

Full install, usage, and build-from-source notes are in [INSTALL.md](INSTALL.md).

To build from source instead:

```bash
lake build                                           # kernel + exe + Mathlib metatheory; 0 sorry
lake exe LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'    # [13]
lake exe LeaTTa --min '!(map-atom (1 2 3) $x (* $x $x))'  # [(1 4 9)]
lake exe LeaTTa --min '!(case (+ 1 1) ((1 one) (2 two)))' # [two]
make release                                         # package dist/leatta-<version>-<platform>.tar.gz
./scripts/run-oracle.sh                              # differential oracle vs Hyperon's corpus, 270/270
```

## Where it improves on the current implementation

The minimal interpreter in `hyperon-experimental` is openly provisional. Its source carries a
self-described "hack" and several `TODO` notes at the points that decide evaluation. This
formalization replaces those with declarative, total constructs. The full table is in the book's
Improvements over Hyperon appendix at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/):

- the mutable `is_evaluated()` bit, commented "a hack" at `interpreter.rs:1142`, becomes static
  return-type gating taken from each function's declared type;
- the `is_variable_op` hotfix (`interpreter.rs:607`) becomes a total `isVariableHeaded` guard;
- `Rc<RefCell>` mutation becomes a pure immutable stack, the global `make_unique` counter becomes a
  threaded pure gensym, and the unbounded loop becomes a fuel-bounded driver with a proved termination
  measure;
- linear rule lookup becomes explicit first-argument indexing.

## Layout and scope

- Active: `Core` (the object language), `Runtime.Parser`, `Minimal.Interpreter`, `Minimal.Stdlib`.
  `Proofs` and `Operational` are the metatheory and the published semantics. `MeTTaIL` (with
  `MeTTaILProofs` and `MeTTaILTests`) is the work-in-progress MeTTa-IL formalization. `CordialMiners` is
  the PoR-weighted Cordial Miners consensus formalization, with its safety metatheory.
- Archived and not built: earlier exploratory models, including a four-register runtime, categorical
  metagraph rewriting, a Ruliad sketch, and an earlier approximate standard library. They live under
  [archive/](archive/) with their own README, kept for reference and not part of the verified work.
- In scope: the minimal interpreter, the standard library (computation, control, lists, sets,
  asserts), the runtime type system, mixed arithmetic, mutable spaces and state, conjunctive match,
  and the metatheory layer.
- TODO: the full module system is not yet covered; the MeTTa-IL formalization is incomplete (its open
  parts are listed in the MeTTaIL section above and in [`MeTTaIL/SPECIFICATION.md`](MeTTaIL/SPECIFICATION.md)).
