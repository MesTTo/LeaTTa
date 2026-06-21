# LeaTTa: machine-checked MeTTa semantics and runtime in Lean 4

LeaTTa 1.0 is a Lean 4 development for MeTTa and the semantics around it. It has three public
surfaces:

- a native `LeaTTa` executable for Hyperon's minimal MeTTa interpreter and standard library;
- a MeTTaIL formalization that can take a small editable dialect file and run terms through the
  generic reducer;
- a Verso book and generated API reference that explain the formalization and expose the checked
  definitions and theorems.

The minimal interpreter follows `hyperon-experimental`: the standard library is written in MeTTa on
top of the same small instruction set. The executable kernel is total and does not import Mathlib.
Mathlib is used in the proof libraries, where the metatheory lives.

The release is meant to be usable as a reference, not only as a proof artifact. It runs Hyperon's own
test files and agrees with them. The active Lean code has no `sorry`, `admit`, `native_decide`,
`partial`, or `unsafe`; CI checks that invariant, the oracle, the regression suite, the book, and the
warning policy. The full comparison with Hyperon is in the book's Improvements over Hyperon appendix
at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## What 1.0 Includes

The 1.0 release covers the minimal interpreter, its standard library, the gradual type system, the
published four-register operational semantics, the MeTTaIL runtime path, and the PoR-weighted
Cordial Miners safety core.

The runtime-facing pieces are:

- `LeaTTa --min`, `--file`, and `--oracle` for the minimal MeTTa interpreter;
- `LeaTTa --mettail FILE --term TERM [--fuel N]` for small editable MeTTaIL dialect files;
- `scripts/run-oracle.sh` for the Hyperon corpus oracle;
- `scripts/run-regression.sh` for focused regression tests, including the MeTTaIL runtime fixture.

The proof-facing pieces are:

- determinism and confluence results for the executable kernel;
- soundness and completeness of first-argument indexing;
- gradual type-soundness results and the non-transitivity example for consistency;
- a bisimulation between the indexed kernel and the published operational semantics at rule-firing
  granularity;
- MeTTaIL elaboration, transformation, reduction, confluence, subject-reduction, OSLF, and
  distributive-law results;
- a Cordial Miners safety theorem reduced to the expected consensus assumptions.

## Quick Test: Editable MeTTaIL Runtime

The fastest way to check the "tweak the LanguageDef, get a runtime" path is the external MeTTaIL
fixture. It declares a tiny boolean dialect:

```text
sort Tm
term tt : Tm
term ff : Tm
term notOp : Tm -> Tm
rewrite notTt : (notOp tt) => ff
rewrite notFf : (notOp ff) => tt
```

The file format is intentionally small. Each non-empty line is one declaration. `#` starts a comment.
`sort Tm` exports a sort, `term notOp : Tm -> Tm` declares a prefix constructor, and
`rewrite notTt : (notOp tt) => ff` declares a base rewrite. The term syntax on the command line is
S-expression syntax over the declared constructors.

From a source checkout, run the fixture and compare stdout with the expected normal form:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt)'
```

Expected output:

```text
ff
```

From a release bundle, use the bundled example file instead:

```bash
bin/LeaTTa --mettail examples/bool.mettail --term '(notOp tt)'
```

Expected output:

```text
ff
```

The opposite rewrite uses the same dialect file:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp ff)' --fuel 100
```

Expected output:

```text
tt
```

A term with no matching rewrite is already in normal form, so it prints back unchanged:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp nope)'
```

Expected output:

```text
(notOp nope)
```

Malformed input is rejected before reduction:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt'
```

Expected stderr:

```text
MeTTaIL term did not parse
```

You can also test a new dialect without changing tracked files:

```bash
tmp=$(mktemp /tmp/mettail-readme.XXXXXX)
printf '%s\n' \
  'sort Tm' \
  'term a : Tm' \
  'term b : Tm' \
  'term step : Tm -> Tm' \
  'rewrite stepA : (step a) => b' > "$tmp"
lake exe LeaTTa --mettail "$tmp" --term '(step a)'
rm -f "$tmp"
```

Expected output:

```text
b
```

The shell regression suite includes the same CLI path:

```bash
./scripts/run-regression.sh
```

Expected tail:

```text
REGRESSION TOTAL: PASS=47 FAIL=0
mettail-runtime: PASS
REGRESSION OK
```

The Lean test target also evaluates the file parser and runtime examples:

```bash
lake build MeTTaILTests
```

Expected MeTTaIL runtime payloads:

```text
Except.ok (some "ff")
Except.ok (some "tt")
Build completed successfully
```

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

The executable kernel builds without Mathlib, and the proof libraries build with the same no-placeholder
policy used by CI.

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

## MeTTaIL: Specs to Runtime

`MeTTaIL/` is a machine-checked formalization of F1R3FLY's MeTTaIL, the meta-language that turns a
presentation of a graph-structured lambda theory into a calculus's grammar, equations, and rewrites. It
is built from the F1R3FLY MeTTaIL repository (<https://github.com/F1R3FLY-io/MeTTaIL>). The formalized
core is now executable: a presentation can be elaborated, monomorphized, and run by the generic reducer.

The checked pipeline has four layers:

- `MeTTaIL/Theory/*` models presentation algebra and elaboration.
- `MeTTaIL/Transform/*` models desugaring, type-lifting, and monomorphization.
- `MeTTaIL/Semantics/*` defines reduction, evaluation contexts, normal forms, sorting, and the OSLF
  predicate model.
- `MeTTaIL/Runtime/*` connects the front end to the reducer, including the small external file format
  used by `--mettail`.

The elaborator and transforms are pinned against output captured from the real Scala tool on
`Rholang.module`, checked by kernel `decide`. The reduction layer proves soundness of executable steps,
normal-form reachability under the strategy, subject reduction for the all-subterms sort system, and
confluence results for the first-order rewriting cases. The MeTTaIL proof target also includes the
rewriting modulo AC machinery, the conditional runtime bridge, the OSLF recurrence and categorical
fragments, and the Beck-style distributive-law theorem used by the spatial logic story.

The shipped `LeaTTa` binary exposes the core runtime path for line-oriented dialect files. That path is
deliberately smaller than the full BNFC MeTTaIL surface: it supports `sort`, `term`, and base
`rewrite` declarations, then runs one S-expression term through `runInstMono`. This gives a concrete
edit-file-run loop for base-rewrite dialects while keeping the richer MeTTaIL parser as future surface
work.

What remains out of scope for 1.0: the modal hypercube typing for binder calculi, the rho-calculus
full-abstraction result, the spice and mq calculi as full reduction theories, a standalone rho-calculus
reduction development, the per-variable category-consistency check in the elaborator, and an
operational bisimulation from MeTTaIL back to the four-register machine. These limits are stated in the
source modules and in the book chapter rather than hidden behind broad claims.

Formalizing the tool also turned up several upstream issues in the Scala implementation. They are
written up for the F1R3FLY team in
[`MeTTaIL/HYPERON_IMPROVEMENTS.md`](MeTTaIL/HYPERON_IMPROVEMENTS.md). The full treatment is the MeTTaIL
chapter in the book at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/). Build it with:

```bash
lake build MeTTaIL MeTTaILProofs MeTTaILTests
```

### The spec-to-runtime claim

For the formal core, the path is:

```text
TheoryInst -> elaborate -> monomorphize -> runInstMono -> normal form
```

For the product-facing file format, the path is:

```text
FILE.mettail -> LanguageFile.parseInst -> runInstMono -> normal form
```

This is the concrete version of the MeTTaIL idea: tweak the LanguageDef-shaped presentation and get a
runtime whose executable steps are checked against the presentation's own reduction relation. The
one-step engine is sound and, for base rewriting, complete; it terminates under a measure and is
confluent by Newman's lemma, with unique normal forms for the deterministic cases.

Rewriting modulo AC is done the full way for binary-curried operators like rho's parallel `|`. There is a
verified total order on terms (`Order`), a canonical form that is sound, complete, and idempotent and so
decides AC-equivalence (`AC`), the modulo-AC engine sound for the `R/AC` relation (`ACEngine`), and
Church-Rosser modulo AC: AC-equivalent terms normalize to the identical term (`ACNormal`). A worked check
confirms the decision procedure collapses commutativity and associativity and keeps distinct terms apart.

The type half has three layers. The grammar induces a head-sort discipline preserved by reduction
(`Sorts`, discharged on a concrete presentation in `SortSoundness`). Deeper, a recursive all-subterms sort
system (`WellSorted`) carries the substitution lemma both ways, the inst half (`inst_wellSorted`) and the
matching half (`SubjectReduction`), which combine into subject reduction for a contraction
(`subjectReduction_base`) and then lift through the one-step and many-step reduction relations
(`rewStep_preserves_wellSorted`, `rewStepMany_preserves_wellSorted`): every subterm keeps its declared sort
along reduction, shown on a variable-carrying rule. And `OSLF` is a machine-checked formalization of the first-order fragment of Stay and Meredith's
"Logic as a Distributive Law": formulae are predicates on terms, the spatial composition is the
distributive law, the behavioral modalities range over reduction, and the lambda arrow is a special case of
the possibly modal operator. The greatest-fixed-point modalities for confinement and safety are in
`OSLFRec`, and `OSLFCat` gives the 2-categorical distributive-law derivation in the thin 2-category that is
the predicate preorder, exactly where the logic lives: the possibility modality is a closure operator (a
monad), the necessity modality the dual interior operator (a comonad), and the spatial composition a
bifunctor. The distributive law is concrete (possibility distributes over disjunction, necessity over
conjunction, a constructor over disjunction), and `composeClosure` is the order-theoretic Beck theorem that
a distributive law of monads yields a composite monad.

Confluence beyond Newman comes from overlap analysis. `CriticalPairs` builds a first-order term model with
positions and proves the full Critical Pair Theorem. Every local peak is dispatched by the position
trichotomy into the disjoint case (the Parallel Moves Lemma), the variable-overlap case
(`localConfluence_variable`, joined via reduce-all-copies and a reduct-matching lemma using left-linearity),
or the critical-pair case (a non-variable overlap found by the positions-of-a-substitution decomposition,
discharged by the joinable-critical-pairs hypothesis). The headline `localConfluent_of_CPJ` says a
left-linear system with joinable critical pairs is locally confluent, and `confluent_of_CPJ` chains it with
Newman's lemma for the Knuth-Bendix-Huet criterion: terminating, left-linear, joinable critical pairs imply
confluence. Supporting results include the congruence of rewriting (a step, and a whole sequence, lift into
any context).

The compile path `runInst`/`runInstMono` (elaborate, monomorphize, run) connects the front end to the
reducer, with monomorphization proved behavior-preserving. `MeTTaIL/Runtime/LanguageFile.lean` is the
product-facing file parser for that path; it is intentionally smaller than the full BNFC MeTTaIL
surface. Everything is axiom-clean (no `sorry`, the three standard axioms only). The remaining research
items are named above and in the MeTTaIL book chapter.

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
tar xzf leatta-1.0.0-linux-x86_64.tar.gz
cd leatta-1.0.0-linux-x86_64 && ./install.sh   # installs to ~/.local/bin
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
- Out of scope for this release: the full module system and the unfinished MeTTa-IL pieces listed in
  the MeTTaIL section above.
