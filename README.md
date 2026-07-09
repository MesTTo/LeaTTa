<!-- SPDX-FileCopyrightText: 2026 MesTTo -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# LeaTTa: machine-checked MeTTa semantics in Lean 4

LeaTTa is a Lean 4 development for MeTTa, the MeTTaIL runtime path, a distributed atomspace model, and
PoR-weighted Cordial Miners. The executable kernel ports Hyperon's minimal MeTTa interpreter, the
small instruction set under the rest of MeTTa. The standard library is written in MeTTa over that
kernel. The runnable interpreter is total, fuel-bounded, and Mathlib-free.

Version `1.0.8` adds the MORK/MM2 resource-readback proof surface on top of the `1.0.7` distributed
atomspace release. The public branch has five checked surfaces:

- the minimal interpreter and standard library run Hyperon's oracle corpus: 270 assertions across 22
  vendored files;
- `Metatheory` and `Operational` prove determinism, confluence of the deterministic fragment, type
  soundness, indexing soundness and completeness, query correspondence, observation records,
  MORK-backed query readback, MM2 lowering, ACT resource isolation, and the published four-register
  machine properties;
- `Distributed` models replica-local atoms, mutation events, vector clocks, fairness as a theorem
  parameter, ordered replay assumptions, and matching convergence;
- `MeTTaIL`, `MeTTaILProofs`, and `MeTTaILTests` formalize the determinate presentation pipeline and
  ship a small editable dialect that runs through the checked reducer;
- `CordialMiners` formalizes the PoR-weighted coarse consensus protocol, proves the top-level safety
  theorem, and hosts the protocol as a MeTTaIL runtime presentation.

The branch does not claim the full Hyperon module system, MeTTa on Rholang, unordered distributed
convergence without replay assumptions, the full MeTTaIL-to-rho theorem, or the remaining denotational
goals. Public theorem targets build with no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`.
The longer Hyperon comparison is in the book appendix at
[mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## Start here

Run the public surfaces from a checkout:

```bash
lake build
lake build Distributed Metatheory Operational
./scripts/run-oracle.sh
./scripts/run-regression.sh
lake build MeTTaIL MeTTaILProofs MeTTaILTests
lake build CordialMiners CordialMiners.Runtime.Run
```

Expected results:

- `lake build` ends with `Build completed successfully`;
- `Distributed`, `Metatheory`, and `Operational` build directly from their public roots;
- `./scripts/run-oracle.sh` reports `ORACLE OK` with 270 passing assertions;
- `./scripts/run-regression.sh` reports `REGRESSION OK`;
- MeTTaIL and Cordial Miners build without forbidden placeholders.

## Quick MeTTaIL runtime check

The executable can run an editable MeTTaIL dialect file. The fixture
[`tests/mettail/bool.mettail`](tests/mettail/bool.mettail) declares:

```text
sort Tm
term tt : Tm
term ff : Tm
term notOp : Tm -> Tm
rewrite notTt : (notOp tt) => ff
rewrite notFf : (notOp ff) => tt
```

Run it:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt)'   # ff
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp ff)' --fuel 100   # tt
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp nope)' # (notOp nope)
```

Malformed input is rejected before reduction:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt'
# stderr: MeTTaIL term did not parse
```

You can test a new dialect without changing tracked files:

```bash
tmp=$(mktemp -t mettail-readme.XXXXXX)
printf '%s\n' \
  'sort Tm' \
  'term a : Tm' \
  'term b : Tm' \
  'term step : Tm -> Tm' \
  'rewrite stepA : (step a) => b' > "$tmp"
lake exe LeaTTa --mettail "$tmp" --term '(step a)'   # b
rm -f "$tmp"
```

The regression suite includes that CLI path:

```bash
./scripts/run-regression.sh
# REGRESSION TOTAL: PASS=47 FAIL=0
# mettail-runtime: PASS
# REGRESSION OK
```

The Lean test target also checks the parser and runtime examples:

```bash
lake build MeTTaILTests
# Except.ok (some "ff")
# Except.ok (some "tt")
# Build completed successfully
```

## Minimal MeTTa kernel

The executable kernel is in `MettaHyperonFull/Minimal/`.

`Interpreter.lean` is a faithful port of `interpreter.rs`: a continuation-passing nondeterministic
stack machine with the thirteen minimal instructions `eval`, `evalc`, `chain`, `unify`, `cons-atom`,
`decons-atom`, `function`, `return`, `collapse-bind`, `superpose-bind`, `metta`, `metta-thread`,
`capture`, and `context-space`. One step is total. The driver is fuel-bounded because MeTTa programs
can diverge.

`Stdlib.lean` implements the standard library in MeTTa over those instructions: `if`, `let`, `let*`,
`switch`, `case`, `map-atom`, `filter-atom`, `foldl-atom`, set operations, assertions, `match`, and
grounded operations.

The implemented runtime surface includes gradual `get-type`, application checking with `(BadArgType
...)`, multi-type symbols, type-variable unification for parametric and dependent signatures, mixed
integer and float arithmetic, named spaces, `add-atom`, `remove-atom`, `get-atoms`, `match` over
`&self` and named spaces, conjunctive `(, ...)` match, state cells, `bind!` tokens, and `import!` as
the only IO. Hyperon represents most of that state through `Rc<RefCell>` mutation. LeaTTa threads a
pure `World` of spaces, state cells, and tokens through evaluation. Sequential file evaluation is
preserved, so each `!` query sees exactly the knowledge base before it.

## Oracle validation

The oracle gate runs Hyperon's unmodified corpus vendored under [tests/corpus/](tests/corpus/) (MIT,
commit `3f76dc4`). An assertion passes when it evaluates to `()`. The script builds the interpreter,
runs every `!` assertion, compares expected output, and exits nonzero on any mismatch.

```bash
./scripts/run-oracle.sh                                    # 270 / 270, ORACLE OK
lake exe LeaTTa --oracle tests/corpus/test_stdlib.metta    # single file
```

| Hyperon test file | result |
|---|---|
| `lib/tests/test_stdlib.metta` | 39 / 39 |
| `a1_symbols`, `a2_opencoggy`, `a3_twoside` | 7 / 7, 1 / 1, 4 / 4 |
| `b0_chaining_prelim`, `b1_equal_chain`, `b2_backchain`, `b3_direct` | 5 / 5, 8 / 8, 6 / 6, 4 / 4 |
| `b4_nondeterm.metta` | 11 / 11 |
| `b5_types_prelim.metta` | 26 / 26 |
| `c1_grounded_basic.metta`, `c3_pln_stv.metta` | 21 / 21, 5 / 5 |
| `c2_spaces.metta` | 25 / 25 |
| `e1_kb_write`, `e2_states`, `e3_match_states` | 3 / 3, 14 / 14, 9 / 9 |
| `d1_gadt.metta`, `d2_higherfunc.metta` | 14 / 14, 25 / 25 |
| `d3_deptypes`, `d4_type_prop`, `d5_auto_types` | 8 / 8, 18 / 18, 7 / 7 |
| `g1_docs.metta` | 10 / 10 |

The passing tier includes GADTs, higher-order functions, dependent length arithmetic, types as
propositions, auto type checking, `get-doc`, and `help!`.

`f1_imports.metta` is excluded because Hyperon marks it Python-mode-only. Its header says it does not
work in no-Python mode because it assumes `&self` starts nearly empty with `corelib` and `stdlib` as
separate modules. LeaTTa ships the prelude inside `&self`. The module behavior it would exercise,
`import!` into named spaces and diamond-dependency deduplication, is covered by `c2_spaces` and
`g1_docs`.

## Proof surface

The kernel proof layer is `MettaHyperonFull/Proofs/`. It uses Mathlib and proves the replay properties
that matter for on-chain MeTTa:

- the abstract machine is deterministic while nondeterminism stays in the result list;
- the deterministic fragment is confluent;
- first-argument rule indexing is sound and complete, including the same-head case where Hyperon's
  `Space::visit` undercounts;
- the gradual type checker is total and reports `BadArgType` only for a real argument type;
- alpha-equivalence is an equivalence relation;
- binding merge laws expose successful, conflicting, and unification-mediated cases;
- atomspace laws cover insert, remove, query, type assignment, equality rules, and threaded-world
  visibility;
- substitution-cycle audit facts state where direct-loop checks stop and recursive resolution needs an
  acyclicity condition;
- host-law records make grounded equality, matching, typing, execution, and display assumptions
  explicit;
- MORK-facing laws cover duplicate-preserving query backends, codecs, decoded binding rows, prepared
  query snapshots, sharded counts, named spaces, grounded host handles, MM2 lowering, and ACT resource
  isolation;
- observation records expose input, fuel, result atoms, error atoms, exhaustion status, and before/after
  worlds without a second evaluator;
- arrow-constructor laws pin `Atom.mkArrow` and `TypeEnv.arrowParts?` to the executable splitter.

`MettaHyperonFull.Operational.*` checks the published Meta-MeTTa operational semantics (arXiv
2305.17218): the four-register machine `(i,k,w,o)`, barbed bisimulation, and a gas-bounded extension.
`Proofs/Correspondence.lean` bridges the indexed kernel to that specification.

`MettaHyperonFull.Distributed.*` is a distributed atomspace proof target, not the Cordial Miners
consensus proof. It models replica-local storage, add/remove events, vector clocks, local issue,
remote delivery, fairness, ordered replay, and convergence. Checked claims include read-your-own-writes,
mid-flight divergence before delivery, append-only logs, barrier extension, quiescent coverage,
vector-clock max as a least upper bound, ordered atom-set convergence under
`OrderedReplayAssumptions`, and matching convergence after ordered replay.

```bash
lake build Distributed
```

## MORK and MM2 layer

The `1.0.8` proof addition models the MORK-facing boundary without importing a byte trie or native host
runtime into the kernel. The core files are:

- `Core/QueryBackend.lean` and `Proofs/QueryBackend.lean`: duplicate-preserving query backends,
  reference backends, generated reference backends, and serial conjunctive-query laws;
- `Core/MorkCodec.lean`, `Core/MorkCompactCodec.lean`, and their proofs: logical and compact
  `newVar`/`varRef` codecs with decode-after-encode laws;
- `Core/MorkEncodedSpace.lean`, `Core/MorkDecodedBindings.lean`, and their proofs: encoded-space query
  refinement, repeated-variable coreference, decoded binding rows, and query/data separation;
- `Core/MorkNamespace.lean`, `Core/MorkNamedSpaces.lean`, `Core/MorkPrepared.lean`,
  `Core/MorkSharded.lean`, and their proofs: query-result namespace separation, named-space
  visibility, snapshot equivalence, prepared-query equivalence, and finite-sharding count laws;
- `Core/MorkGroundedFilter.lean`, `Core/MorkGroundedRegistry.lean`, and their proofs: mutable grounded
  rows filtered by stable live values and host handles;
- `Core/MorkMM2.lean`, `Core/MorkMM2Lowering.lean`, `Core/MorkMM2Resources.lean`, and their proofs:
  semantic MM2 exec consumption, lowering for `I`/`,` sources and `O`/`,` templates, equality and
  inequality source constraints, add/remove effects, priority-ordered exec selection, and a pure ACT
  resource boundary where resource names stay isolated from the main reference `Space`.

The layer intentionally does not claim byte-level path priority, mmap ACT files, host solver callbacks,
WASM/native resources, lock scheduling, or the byte trie store.

## MeTTaIL and rho-facing research

`MeTTaIL/` formalizes the determinate part of F1R3FLY's Meta Type Talk Intermediate Language
(<https://github.com/F1R3FLY-io/MeTTaIL>). A presentation declares sorts, constructors, equations, and
rewrites for an object calculus. LeaTTa checks the presentation pipeline and runs the resulting rewrite
system through a verified reducer.

Checked today:

- elaborate, desugar, type-lift, and monomorphize, pinned by `decide` against output captured from the
  Scala tool on `Rholang.module`;
- the GSLT reduction relation and soundness theorem;
- subject reduction and confluence for SKI and simply typed lambda calculus presentations;
- spice bounded reachability and mq-calculus Born-rule probability conservation;
- the MeTTa-to-GSLT bridge and presentation lattice laws;
- an executable reducer generated from a presentation;
- the AC-aware runtime fragment used by Cordial Miners;
- labelled transition systems, simulation, bisimulation, denotational kernels, context congruence,
  full abstraction, observational calibration, path-key RSpace branches, and costed transition systems;
- red/black reflective universes, quote/drop round trips, a generic final-coalgebra surface, and a
  bridge from final-behaviour models to `FullyAbstractModel`;
- the rset hereditarily finite core, colour automaton, atom opacity, red/black swap, finite support for
  atom renaming, extensional quotient, and union laws;
- the interacting trie-map surface `RITM = ITM[RITM, 1 + RITM, RITM]` and Jetta-style packed binding
  addresses comparable with path-key RSpace prefixes;
- rho syntax, quote/drop, ordinary and persistent send/receive COMM, `|` structural congruence, a
  one-channel RSpace boundary, and the K-shaped `<In>`/`<Out>` machine cases for the four persistence
  combinations;
- the first packet-level MeTTaIL-to-rho compiler bridge. A successful `applyBaseRewrite` is a real
  `Reduces` step, emits the encoded contractum at the source term location, and reifies the packet
  listener as a ready K communication step modulo `| 0`.

The public source references for the rho side are the F1R3FLY f1r3node reducer
(<https://github.com/F1R3FLY-io/f1r3node/blob/dylon/mettatron/rholang/src/rust/interpreter/reduce.rs>)
and the direct-rule compiler shape in `mettail-rust` branch `GSLT2rho`
(<https://github.com/F1R3FLY-io/mettail-rust/blob/GSLT2rho/gslt2rho/rho_compile/src/compile.rs>).
LeaTTa uses those as implementation guides, not as completed semantics.

Other MeTTaIL research surfaces are present as interfaces:

- `RSet.lean` covers the finite red/black set core from the rset paper and still leaves the recursive
  element quotient, algebraic-set-theory fixpoint, and final behaviour coalgebra open;
- `Denotational.lean` states labelled transition, bisimulation, full abstraction, path-key RSpace, and
  costed-system transfer theorems but does not construct the knotted topos, trie store, cut law, cost
  endofunctor, or language-specific calibration theorem;
- `CostRoundTrip.lean` states the continued-cost wrapper, starved-deadlock theorem, wrapped trace
  preservation, unit-token cost, and `T o C` image/fixed-point theorem;
- `Native.lean`, `NativeGrammar.lean`, and `NativeTypes.lean` state the native carrier, native
  grammatical-formalism, and OSLF native-type obligations. The grammar source is the public MeTTapedia
  GF/OSLF paper
  (<https://github.com/zariuq/MeTTapedia/blob/main/papers/native-grammatical-formalism.pdf>).
  These files define the interface a GF or MeTTaIL frontend has to instantiate. They are not a GF
  parser and do not import MeTTapedia;
- `Hypercube.lean` checks the finite modal/spatial center: sort slots, executable equation filters,
  explicit slot constraints, generated rule schemes, judgment footprints, and footprint containment.
  Generated typing rules and subject reduction are future work;
- `KnottedUniverse.lean` states reflective red/black universes, quote/drop equivalences,
  structure-preserving morphisms, coalgebras for a type endofunctor, and the terminal-coalgebra witness
  shape. It does not construct the knotted topos.

Build the layer with:

```bash
lake build MeTTaIL MeTTaILProofs MeTTaILTests
```

The axiom audit for this layer reports only the standard axioms used elsewhere in the project:
`propext`, `Classical.choice`, and `Quot.sound`.

### Verified spec-to-runtime path

The CLI file path goes from a small presentation file to a running reducer: parse declarations,
monomorphize, run the term through the checked evaluator, and print the normal form. The one-step
engine is sound and, for base rewriting, complete. It terminates under a checked measure and is
confluent by Newman's lemma when termination and local confluence are supplied.

The AC layer gives a verified total order on terms, canonical forms that decide AC-equivalence,
modulo-AC stepping sound for `R/AC`, and Church-Rosser modulo AC. `ACMatch` proves the scoped matcher
used by Cordial Miners: one fixed subpattern plus one rest variable, following Eker's elementary AC
matching and Dundua, Kutsia, and Marin's variadic equational matching.

The type layer gives head-sort preservation, all-subterms well-sortedness, substitution lemmas,
matching lemmas, and subject reduction for one-step and many-step reduction. `OSLF`, `OSLFRec`, and
`OSLFCat` formalize the first-order spatial and behavioural logic layer from "Logic as a Distributive
Law": possibility as closure, necessity as interior, spatial composition as a bifunctor, and the
order-theoretic Beck theorem for composing closures.

`CriticalPairs` proves the Critical Pair Theorem for a first-order term model with positions. Local
peaks split into disjoint, variable-overlap, or critical-pair cases, yielding the Knuth-Bendix-Huet
criterion: terminating, left-linear systems with joinable critical pairs are confluent.

`MeTTaIL/Runtime/LanguageFile.lean` is the checked CLI file format. It is not the full BNFC MeTTaIL
surface. The remaining research items are in module headers and the proof-status appendix.

## Cordial Miners

`CordialMiners/` formalizes PoR-weighted Cordial Miners, a leaderless DAG-based BFT consensus protocol
(arXiv 2205.09174), using the weighted Proof-of-Reputation variant from a Ben Goertzel blueprint.

The headline theorem is `end_to_end_safety_of_finality_permanence`: under a Byzantine-weight bound,
honest non-equivocation, and finality permanence, the protocol never finalizes conflicting values and
correct miners never publish conflicting positions. Prefix monotonicity is derived. The proof passes
through weighted-overlap arithmetic, threshold finality, blocklace closure, equivocation detection,
final-leader ratification, verified topological sorting, a coarse/fine simulation, lossless extraction
to MeTTaIL atoms, executable demos, and the runtime bridge.

```bash
lake build CordialMiners
lake build CordialMiners.Runtime.Run
```

Expected runtime checks:

```text
info: CordialMiners/Runtime/Run.lean:88:0: true
info: CordialMiners/Runtime/Run.lean:121:0: true
info: CordialMiners/Runtime/Run.lean:223:0: true
```

The runtime bridge encodes protocol facts and input events into `MeTTaIL.AST`, defines `cmPresentation`
with six AC-marked coarse rewrite rules, and runs them with `evalAC'`. The main forward theorem is:

```lean
trec_step_forward_decode :
  TrecState.Step s s' ->
  ∃ events target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    astToState dW dH target = s'
```

The backward theorem says a shaped runtime step modulo AC decodes either to one coarse step or to the
same coarse state, provided field decoders respect `ACEq acOpCM`. The executable Nat/Nat instance
discharges that condition as `dNat_acEq` and instantiates `runtime_step_backward_nat`.

Reader-facing details are in [CordialMiners/README.md](CordialMiners/README.md) and
[CordialMiners/Runtime/README.md](CordialMiners/Runtime/README.md).

## Documentation and book

The published site at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/) contains:

- the Verso book at the site root;
- the doc-gen4 API reference at [/api](https://mestto.github.io/LeaTTa/api/), with Mathlib references
  linked to official Mathlib documentation.

The book source is in [book/](book/). It covers the object language, interpreter, type system,
metatheory, operational semantics, kernel correspondence, blockchain angle, distributed atomspace,
MeTTaIL, Cordial Miners, future work, and limitations. Build it separately:

```bash
cd book
lake exe docs
python3 -m http.server 8137 --directory _out/html-multi
```

Open `http://localhost:8137/` or `book/_out/html-multi/index.html`.

## Install and run

The release binary is a single native `LeaTTa` executable. It links only against the standard C library,
so a Linux x86_64 bundle does not require the Lean toolchain.

```bash
tar xzf leatta-1.0.8-linux-x86_64.tar.gz
cd leatta-1.0.8-linux-x86_64
./install.sh
LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'   # [13]
```

Full install and source-build notes are in [INSTALL.md](INSTALL.md).

Build from source:

```bash
lake build
lake exe LeaTTa --min '!(+ 1 (* 2 (- 10 4)))'                 # [13]
lake exe LeaTTa --min '!(map-atom (1 2 3) $x (* $x $x))'      # [(1 4 9)]
lake exe LeaTTa --min '!(case (+ 1 1) ((1 one) (2 two)))'     # [two]
make release
./scripts/run-oracle.sh
```

## Where LeaTTa improves the current interpreter

The minimal interpreter in `hyperon-experimental` is marked provisional at several decision points.
LeaTTa replaces those points with total checked constructs:

- the mutable `is_evaluated()` bit, commented as a hack in `interpreter.rs`, becomes static
  return-type gating from the declared function type;
- the `is_variable_op` hotfix becomes a total `isVariableHeaded` guard;
- `Rc<RefCell>` mutation becomes a pure immutable stack;
- the global `make_unique` counter becomes a threaded pure gensym;
- the unbounded loop becomes a fuel-bounded driver with a checked termination measure;
- linear rule lookup becomes explicit first-argument indexing.

The full comparison table is in the book appendix.

## Layout and scope

- Active kernel: `MettaHyperonFull/Core`, `MettaHyperonFull/Runtime.Parser`,
  `MettaHyperonFull/Minimal.Interpreter`, and `MettaHyperonFull/Minimal.Stdlib`.
- Active proofs: `MettaHyperonFull/Proofs`, `MettaHyperonFull/Operational`,
  `MettaHyperonFull/Distributed`, MORK/MM2 proof modules, MeTTaIL proof modules, and Cordial Miners.
- Runtime presentations: `MeTTaIL`, `MeTTaILTests`, `CordialMiners.Runtime`.
- Archived and not built: earlier exploratory four-register runtime, categorical metagraph rewriting,
  Ruliad sketches, and an earlier approximate standard library under [archive/](archive/).
- In scope: minimal interpreter, standard library, runtime type system, mixed arithmetic, mutable
  spaces and state, conjunctive match, metatheory, published operational semantics, distributed
  atomspace, MORK/MM2 query/resource proof interfaces, MeTTaIL runtime path, and Cordial Miners safety.
- Open: full Hyperon module system, unordered distributed convergence without replay assumptions,
  full MeTTaIL-to-rho theorem, full Rholang/RSpace runtime semantics, trie storage, cut law, cost
  endofunctor, and language-specific observational calibration.
