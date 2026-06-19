# MeTTa minimal interpreter: a machine-checked reference semantics in Lean 4

This is a Lean 4 formalization of Hyperon's minimal MeTTa interpreter, the small "assembly language"
that the rest of MeTTa is built on. The standard library is written in MeTTa on top of those
instructions, the same way `hyperon-experimental` does it. The kernel is total and has no
dependencies: no Mathlib, no Batteries.

The aim is simple. This should be a reference the Hyperon developers can actually use. It runs
Hyperon's own test files and agrees with them, every function is total (no `partial`, no `sorry`, no
`unsafe`), and wherever it differs from the current implementation, it differs by being cleaner. The
full comparison is in [IMPROVEMENTS_OVER_HYPERON.md](IMPROVEMENTS_OVER_HYPERON.md).

## The faithful core

Everything that matters lives in `MettaHyperonFull/Minimal/`:

- `Interpreter.lean` is a faithful port of `interpreter.rs`. It is the continuation-passing,
  nondeterministic stack machine with all twelve minimal instructions (`eval`/`evalc`, `chain`,
  `unify`, `cons-atom`/`decons-atom`, `function`/`return`, `collapse-bind`/`superpose-bind`, `metta`,
  `context-space`, and the `=`-rule query). One step is a total function, and the driver is
  fuel-bounded with a termination measure that Lean checks. MeTTa can legitimately loop forever, so
  the bound is explicit rather than hidden.
- `Stdlib.lean` is the standard library, written as MeTTa over those twelve instructions: `if`,
  `let`, `let*`, `switch`, `case`, `map-atom`, `filter-atom`, `foldl-atom`, the set operations, the
  `assert*` family, `match`, and so on, together with the grounded operations.

The whole faithful library builds in 36 jobs, with 0 `sorry`, 0 `partial`, and 0 `unsafe`.

## How it is validated

The honest test is whether it agrees with Hyperon, so it runs as a differential oracle against
Hyperon's own unmodified test corpus, vendored under [tests/corpus/](tests/corpus/) (MIT, commit
`3f76dc4`). One command builds the interpreter, runs every `!`-assertion in all 22 files, and checks
each result. An assertion passes when it evaluates to `()`, and the script exits non-zero on any
mismatch, so it doubles as the regression gate.

```bash
./scripts/run-oracle.sh                                       # 270 / 270, ORACLE OK
lake exe metta_full --oracle tests/corpus/test_stdlib.metta   # or a single file
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

These are Hyperon's tests, run unmodified, not a subset I picked out. What passes includes the full
dependent-type tier (`d1`–`d5`): GADTs, higher-order functions, dependent length arithmetic, types as
propositions, and auto type-checking, along with the documentation operators `get-doc` and `help!`.

One file is left out: `f1_imports.metta`. Hyperon marks it Python-mode-only (its header says it
"won't work under no python mode"), because it assumes `&self` starts nearly empty with `corelib` and
`stdlib` as separate modules, while this build ships the prelude inside `&self`. The module machinery
it would exercise, `import!` into named spaces and diamond-dependency deduplication, is covered anyway
by `c2_spaces` (25/25) and `g1_docs` (10/10).

## What is implemented

All of this is faithful to Hyperon and built on the minimal interpreter:

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

On top of the running interpreter there is a machine-checked metatheory layer in
`MettaHyperonFull/Proofs/`. This part uses Mathlib and keeps 0 `sorry`, 0 `admit`, and 0
`native_decide`. It proves the things an on-chain MeTTa actually needs, rather than asserting them:

- the abstract machine is deterministic, with all nondeterminism kept in the result list rather than
  the transition relation, which is what replayability needs;
- its deterministic fragment is confluent;
- first-argument rule indexing is sound and complete, so it offers exactly the rules that can fire.
  This is the same-head case where Hyperon's `Space::visit` undercounts (issue #1079);
- the gradual type checker is total, and reports `BadArgType` faithfully and only with a real argument
  type, so it never invents an error;
- α-equivalence is an equivalence relation.

There is also a separate `MettaHyperonFull.Operational.*` library that machine-checks the published
Meta-MeTTa operational semantics (arXiv 2305.17218): the four-register machine ⟨i,k,w,o⟩, its barbed
bisimulation, and a resource-bounded (gas) extension. The bridge between the indexed kernel and that
specification is in `Proofs/Correspondence.lean`. See
[SEMANTICS_CORRESPONDENCE.md](SEMANTICS_CORRESPONDENCE.md).

## The book

There is a longer, textbook-style treatment of all of this in [`book/`](book/), built with Verso. It
walks through the object language, the interpreter, the type system, the metatheory, the operational
semantics and its correspondence to the kernel, and the blockchain angle. It is its own small Lean
project, so you build it on its own:

```bash
cd book
lake exe docs                                               # builds the book
```

The generated site lands in `book/_out/html-multi/`. To read it, open that folder's `index.html` in a
browser, or serve it locally:

```bash
python3 -m http.server 8137 --directory book/_out/html-multi   # then open http://localhost:8137/
```

## Build and run

```bash
lake build                                           # kernel + exe + Mathlib metatheory; 0 sorry
lake exe metta_full --min '!(+ 1 (* 2 (- 10 4)))'    # [13]
lake exe metta_full --min '!(map-atom (1 2 3) $x (* $x $x))'  # [(1 4 9)]
lake exe metta_full --min '!(case (+ 1 1) ((1 one) (2 two)))' # [two]
./scripts/run-oracle.sh                              # differential oracle vs Hyperon's corpus, 270/270
```

## Where it improves on the current implementation

The minimal interpreter in `hyperon-experimental` is openly provisional. Its source carries a
self-described "hack" and several `TODO` notes right at the points that decide evaluation. This
formalization swaps those for declarative, total constructs. The full table is in
[IMPROVEMENTS_OVER_HYPERON.md](IMPROVEMENTS_OVER_HYPERON.md); in short:

- the mutable `is_evaluated()` bit, commented "a hack" at `interpreter.rs:1142`, becomes static
  return-type gating taken from each function's declared type;
- the `is_variable_op` hotfix (`interpreter.rs:607`) becomes a total `isVariableHeaded` guard;
- `Rc<RefCell>` mutation becomes a pure immutable stack, the global `make_unique` counter becomes a
  threaded pure gensym, and the unbounded loop becomes a fuel-bounded driver with a proved termination
  measure;
- linear rule lookup becomes explicit first-argument indexing.

## Layout and scope

- Active and faithful: `Core` (the object language), then `Runtime.Parser`, then
  `Minimal.Interpreter`, then `Minimal.Stdlib`. `Proofs` and `Operational` are the metatheory and the
  published semantics.
- Archived and not built: earlier exploratory models, namely a four-register runtime, categorical
  metagraph rewriting, a Ruliad sketch, and an earlier approximate standard library. They live under
  [archive/](archive/) with their own README, kept for the record rather than as part of the verified
  work.
- In scope: the minimal interpreter, the standard library (computation, control, lists, sets,
  asserts), the runtime type system, mixed arithmetic, mutable spaces and state, conjunctive match,
  and the metatheory layer. Not yet covered: the full module system.
