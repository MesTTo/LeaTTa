# LeaTTa: machine-checked MeTTa semantics in Lean 4

LeaTTa is a Lean 4 development for MeTTa, MeTTaIL, and a checked Cordial Miners runtime. LeaTTa starts
from Hyperon's minimal MeTTa interpreter, the small instruction set that the rest of MeTTa is built on. The
standard library is written in MeTTa on top of those instructions, following `hyperon-experimental`.
The executable kernel is total and has no Mathlib or Batteries dependency.

The release has three active layers.

- The minimal interpreter and standard library run Hyperon's own oracle corpus: 270 passing assertions
  across 22 files.
- The MeTTaIL layer formalizes the determinate presentation pipeline and ships a small editable dialect
  format that runs through the checked reducer.
- The Cordial Miners layer formalizes the PoR-weighted coarse protocol, proves the top-level safety
  theorem, and hosts the protocol as a MeTTaIL runtime presentation.

LeaTTa 1.0.3 is a research release with a fixed list of checked claims. The release does not claim the
full Hyperon module system, MeTTa on Rholang, or the remaining MeTTaIL denotational goals. The theorems
named in this README are checked by Lean's kernel with no `sorry`, no `admit`, no `native_decide`, no
`partial`, and no `unsafe`. The full comparison with Hyperon is in the book's Improvements over Hyperon
appendix at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## Start here

These commands exercise the main public surfaces. They are the fastest way to check that a checkout or
release archive is healthy.

```bash
lake build
./scripts/run-oracle.sh
./scripts/run-regression.sh
lake build MeTTaIL MeTTaILProofs MeTTaILTests
lake build CordialMiners CordialMiners.Runtime.Run
```

Expected results:

- `lake build` ends with `Build completed successfully`.
- `./scripts/run-oracle.sh` reports `ORACLE OK` with 270 passing assertions.
- `./scripts/run-regression.sh` reports `REGRESSION OK`.
- the MeTTaIL and Cordial Miners targets build without forbidden placeholders.

## Quick test: editable MeTTaIL runtime

The fastest way to check the MeTTaIL runtime path is the external dialect fixture. The fixture declares
a tiny boolean language:

```text
sort Tm
term tt : Tm
term ff : Tm
term notOp : Tm -> Tm
rewrite notTt : (notOp tt) => ff
rewrite notFf : (notOp ff) => tt
```

Run the fixture and compare stdout with the expected normal form:

```bash
lake exe LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt)'
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

- `Interpreter.lean` is a faithful port of `interpreter.rs`. The file is the continuation-passing,
  nondeterministic stack machine with all thirteen minimal instructions (`eval`/`evalc`, `chain`,
  `unify`, `cons-atom`/`decons-atom`, `function`/`return`, `collapse-bind`/`superpose-bind`, `metta`,
  `metta-thread`, `capture`, `context-space`). One step is a total function, and the driver is
  fuel-bounded with a termination measure that Lean checks. MeTTa can legitimately loop forever, so
  the bound is explicit rather than hidden.
- `Stdlib.lean` is the standard library, written as MeTTa over those thirteen instructions: `if`,
  `let`, `let*`, `switch`, `case`, `map-atom`, `filter-atom`, `foldl-atom`, the set operations, the
  `assert*` family, `match`, and so on, together with the grounded operations.

The whole library builds with 0 `sorry`, 0 `partial`, and 0 `unsafe`.

## How it is validated

Validation checks agreement with Hyperon. The oracle runs against Hyperon's own unmodified test corpus,
vendored under [tests/corpus/](tests/corpus/) (MIT, commit `3f76dc4`). One
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
(`d1`-`d5`): GADTs, higher-order functions, dependent length arithmetic, types as propositions, and
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

The metatheory layer lives in `MettaHyperonFull/Proofs/`. The layer uses Mathlib and keeps 0 `sorry`, 0
`admit`, and 0 `native_decide`. The layer proves what an on-chain MeTTa needs:

- the abstract machine is deterministic, with all nondeterminism kept in the result list rather than
  the transition relation, which is what replayability needs;
- its deterministic fragment is confluent;
- first-argument rule indexing is sound and complete, so it offers exactly the rules that can fire.
  The theorem covers the same-head case where Hyperon's `Space::visit` undercounts (issue #1079);
- the gradual type checker is total, and reports `BadArgType` faithfully and only with a real argument
  type, so it never invents an error;
- α-equivalence is an equivalence relation.

A separate `MettaHyperonFull.Operational.*` library machine-checks the published Meta-MeTTa
operational semantics (arXiv 2305.17218): the four-register machine ⟨i,k,w,o⟩, its barbed
bisimulation, and a resource-bounded (gas) extension. The bridge between the indexed kernel and that
specification is in `Proofs/Correspondence.lean`, covered in the book's operational-semantics and
correspondence chapters at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/).

## MeTTaIL and the checked runtime

`MeTTaIL/` formalizes the determinate part of F1R3FLY's Meta Type Talk Intermediate Language, built from
the public MeTTaIL repository (<https://github.com/F1R3FLY-io/MeTTaIL>). MeTTaIL is a language for
presenting graph-structured lambda theories. A presentation gives the sorts, constructors, equations,
and rewrites of an object calculus. LeaTTa checks that presentation pipeline and then runs the resulting
rewrite system with a verified reducer.

The runtime claim is the part you can run today: edit a small dialect file, run the `LeaTTa` binary on a
term, and get the normal form produced by the checked evaluator. The larger research claim is still open.
The repo now states the Lean interface that claim has to satisfy: a finitely presentable MeTTaIL/GSLT
should desugar to rho, inherit a fully abstract denotation from the knotted-topoi model, and prove that
denotational equality is exactly context bisimilarity.

What is checked now:

- the elaborate, desugar, type-lift, and monomorphize pipeline, pinned by kernel `decide` against
  output captured from the real Scala tool on `Rholang.module`;
- the GSLT reduction relation and its soundness theorem;
- subject reduction and confluence for SKI and the simply-typed lambda calculus;
- the semantic cores of the two paper calculi: spice bounded reachability and mq-calculus Born-rule
  probability conservation;
- the MeTTa-to-GSLT bridge and the presentation lattice laws;
- the executable reducer generated from a presentation;
- the AC-aware runtime fragment used by Cordial Miners;
- the denotational-semantics interface for labelled transition systems, bisimulation, context
  congruence, full abstraction, and observational calibration;
- the red/black reflective-universe interface: four sorts, quote/drop round trips, a generic
  final-coalgebra surface, and a bridge from final-behaviour models to `FullyAbstractModel`;
- the finitary rset core: red finite sets whose atoms are black finite sets, black finite sets whose
  atoms are red finite sets, an explicit two-state colour automaton, opacity of atoms under same-colour
  membership, red/black colour-swap equivalences, and the finite-support theorem for atom renaming;
- the interacting trie-map surface: the reflective `RITM ::= ITM[RITM, 1 + RITM, RITM]`
  equation and Jetta-style packed binding addresses that fit the path-key RSpace prefix interface;
- a rho target fragment: names, quote/drop, ordinary and persistent send/receive COMM, structural
  congruence for `|`, and the one-channel RSpace produce/consume shape used by the local `f1r3node`
  runtime;
- a K-shaped rho machine fragment: `<In>` and `<Out>` cells for ordinary receives, persistent receives,
  ordinary outputs, and persistent outputs, with theorems that the checked K steps reify to rho COMM
  modulo `|` structure;
- the first packet-level MeTTaIL-to-rho compiler bridge: when `applyBaseRewrite` produces a
  contractum, Lean proves the corresponding `Reduces` step, reifies the packet/listener process as the
  source K cells modulo `| 0`, proves the ready K communication step, and proves the rho listener
  emission of the encoded contractum;
- the axiom-audited theorem surface for those claims.

The MeTTaIL layer builds with 0 `sorry`, 0 `admit`, 0 `native_decide`, 0 `partial`, and 0 `unsafe`. The
axiom audit shows only the three standard axioms used elsewhere in the project: `propext`,
`Classical.choice`, and `Quot.sound`.

What is still missing is also stated directly. The release does not claim the modal hypercube typing
theorem for binder calculi, the rho-calculus full-abstraction theorem, spice and mq as full reduction
theories, a full f1r3node/RSpace operational model, the per-variable category-consistency check in the
elaborator, or an operational bisimulation against the four-register machine. The module headers and the
book keep those boundaries visible.

The denotational and compiler target comes from the F1R3FLY publication set. The core route uses the
rset knotted-universe paper (<https://github.com/F1R3FLY-io/publications/tree/main/rset>), the rho
model (<https://github.com/F1R3FLY-io/publications/blob/main/denotational-semantics-for-rho/knot-rho.pdf>),
and the knotted-topoi lift
(<https://github.com/F1R3FLY-io/publications/blob/main/knotted-topoi/knotted-topoi.pdf>): a finitely
presentable MeTTaIL/GSLT presentation desugars to rho by persistent listeners at term locations, rho
receives a context-labelled behavioural semantics, and equality in the final behaviour object is context
bisimilarity. The path-key RSpace paper
(<https://github.com/F1R3FLY-io/publications/blob/main/polymorphic-rspace/paths-subspaces.pdf>) refines
the store key from names to paths, so prefix comparability becomes part of the matching story. The cost
papers
(<https://github.com/F1R3FLY-io/publications/blob/main/cost-accounting-as-monad/continued-gslt-cost-v2.pdf>,
<https://github.com/F1R3FLY-io/publications/blob/main/cost-accounting/cost-accounted-rho.pdf>) give the
phlogiston/token-stack refinement.

The rset paper now has a direct Lean surface.
`MeTTaIL/Semantics/RSet.lean` formalizes the hereditarily finite core the paper marks as the first
rigorous target. A red finite set contains red nested sets and atoms supplied by black finite sets; the
black copy mirrors that. The checked theorems say that the two-state colour automaton has no self-loop,
quoted atoms round-trip through `dropAtom`, atoms stay opaque to same-colour membership, red and black
finite sets are equivalent by colour swap, and any atom renaming that fixes the atoms occurring in a set
leaves that set unchanged. The file also defines exact-member extensional equality, the corresponding
quotient type, and the finite union laws at that extensional level: empty is neutral, union is
idempotent, commutative, and associative. The `reflective_*` bridge theorems pin the generic
`ReflectiveUniverse` fields to the concrete rset quote/drop and colour-swap functions. The file still
does not build the recursive element quotient needed for the FM representation theorem, construct the
algebraic-set-theory fixpoint, or build the final behaviour coalgebra in the knotted topos.

The store side also has implementation sources. The ITM sketch
(<https://github.com/F1R3FLY-io/itm/blob/main/src/main/scala/syntax/state.scala>) writes the domain
equations for interacting trie maps, including the reflective `RITM` specialization. CZ2
(<https://github.com/Adam-Vandervorst/CZ2>) gives the prefix-compressed storage direction. Jetta
(<https://github.com/trueagi-io/jetta>) gives a concrete packed-index design where a match binding is a
store index plus an atom path inside that stored expression.

`MeTTaIL/Semantics/Denotational.lean` writes the usable part of that target as Lean definitions and
transfer theorems. The file defines labelled transition systems, simulations, bisimulations,
denotational kernels, context congruence, the `FullyAbstract` property, calibration from
context-labelled bisimilarity to object-language observational equivalence, a pullback theorem for
transferring full abstraction along a translation that preserves and reflects bisimilarity,
`PathRSpace` for path keys and subspace COMM branches, and `Costed` for costed transition systems whose
traces forget to ordinary behaviour traces. The file does not construct the knotted topos, prove the
MeTTaIL-to-rho operational correspondence, formalize the trie store, prove the cut distributive law,
construct the cost endofunctor, or instantiate the observational-calibration theorem for each object
language.

`MeTTaIL/Semantics/KnottedUniverse.lean` adds the checked red/black surface that the rset, rho, and
knotted-topoi papers need. It defines the colours, the four visible sorts, the two quote/drop
equivalences, a `TypeEndofunctor`, and the category of coalgebras for that functor. `FinalCoalgebra`
produces `FinalCoalgebra.isTerminal`, a Mathlib `IsTerminal` witness for the terminal
coalgebra in that category. `FinalBehaviourModel.toFullyAbstractModel` says that once the final
behaviour map has the right kernel and context congruence proof, it is exactly the existing
full-abstraction package. The file does not construct the knotted topos or prove that the real rho
behaviour functor has a final coalgebra.

`MeTTaIL/Semantics/InteractingTrieMap.lean` adds the checked ITM surface. It separates the ITM
polynomial layer from the reflective fixed point, so Lean can state the equation without a
same-universe nested-inductive problem. The audited theorems prove that `RITM` rolls and unrolls to one
layer of `ITM[RITM, 1 + RITM, RITM]` and that a Jetta-style packed binding address is comparable with
its store root in the path-key RSpace prefix order. The file still
does not implement the prefix-compressed trie store, the cut law, or the final behaviour coalgebra.

`MeTTaIL/Semantics/Rho.lean` adds the first rho-side checked target. It defines the rho syntax, name
substitution, quote/drop, ordinary and persistent send/receive COMM, structural congruence for parallel
composition, and a small RSpace boundary where a one-channel consume matches a produced payload. The
local implementation source for that boundary is
`/home/user/Dev/mettatron-workspace/f1r3node/rholang/src/rust/interpreter/reduce.rs`:
`eval_send` evaluates and substitutes the channel and data before `produce`, `produce` stores a
`ListParWithRandom`, `consume` installs a `TaggedContinuation`, both carry persistent flags, and the
matcher lives under `rholang/src/rust/interpreter/matcher/`. The old K semantics is also in that repo,
under `rholang/src/main/k/rholang/`. Its README says that K version is unfinished and points to newer
K work elsewhere, so LeaTTa uses it as an operational staging guide, not as a finished reference
semantics. It still gives concrete structure:
`configuration.k` has `<In>`, `<Out>`, `<subst>`, and global candidate-ID cells;
`sending-receiving.k` covers ordinary send/receive; `persistent-sending-receiving.k` separates
persistent send `!!`, persistent receive `for (... <= C) { Q }`, and the persistent/persistent loop
case; `specific-matching-rules.k` shows standard matching as substitution through `<subst>`; and
`matching-with-par.k` has the separate par-matching machine. `MeTTaIL/Semantics/RhoKMachine.lean` now
models the four one-channel COMM cases: ordinary input with ordinary output, ordinary input with
persistent output, persistent input with ordinary output, and persistent input with persistent output.
It defines K-style input and output cells with IDs, candidate sets, and the local `ReadyPair` guard:
`CandidatePair` from `<InData>` and `<OutData>`, plus `MatchedOne` for the result of
`aritymatch["STDMATCH"]` on the one-message payload. It then proves that each branch reifies to rho COMM
modulo parallel structure. It also models the one-pair creation rules that move a surface input or
output into a K cell and record candidates from the current global ID lists; those creation steps
preserve the reified rho process by `Rho.KMachine.creation_to_struct`. The named COMM branch theorems
are `Rho.KMachine.ordinaryReceive_to_rho`, `Rho.KMachine.persistentOutput_to_rho`,
`Rho.KMachine.persistentReceive_to_rho`, and `Rho.KMachine.persistentBoth_to_rho`. The file does not yet
model full multi-cell ID maintenance, the full K matcher, the par matcher, or the repeated scheduling
discipline behind the persistent/persistent loop.

`MeTTaIL/Semantics/RhoCompiler.lean` is the first checked compiler bridge. It follows the direct-rule
shape in `/tmp/mettail-rust-GSLT2rho/gslt2rho/rho_compile/src/compile.rs`: a rule has a persistent
listener on a rule channel, and a matched contractum is sent as a packet. The theorem
`Rho.Compiler.applyBaseRewrite_reduces_and_emits` says that a successful `applyBaseRewrite` result is a
real MeTTaIL `Reduces` step and that the rho listener emits `encodeAST` of the contractum at the source
term location. The same file now also proves `Rho.Compiler.contractum_kstep`: the contractum packet is
a K-machine persistent-receive step whose `ReadyPair` proof comes from the packet channel, and
uses `Rho.KMachine.acceptAny` because `applyBaseRewrite` has already produced the matched contractum.
`Rho.Compiler.contractumRun_struct_kSource` identifies the actual packet/listener rho process with the
created K cells, up to the trailing `| 0` introduced by the K configuration renderer.
`Rho.Compiler.contractumRun_kstep_to_rho` starts from that actual packet/listener process and takes the
ready K communication step modulo `|` laws. The combined theorem
`Rho.Compiler.applyBaseRewrite_reduces_emits_and_reifies_kstep` packages the three checked facts:
MeTTaIL reduction, ready K communication, and rho emission. It does not prove the full matcher/router,
contextual channel compiler, binder freshness discipline, or two-direction operational correspondence.

Formalizing the tool also turned up several bugs in it. They are written up for the F1R3FLY team in
[`MeTTaIL/HYPERON_IMPROVEMENTS.md`](MeTTaIL/HYPERON_IMPROVEMENTS.md). The full treatment is the MeTTaIL
chapter in the book at [mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/). Build it with the
rest of the proofs:

```bash
lake build MeTTaIL MeTTaILProofs MeTTaILTests
```

### A verified spec-to-runtime

The formalization carries a presentation all the way to a running reducer. Change the declarations in the
small CLI format, and the `LeaTTa` binary parses the file, monomorphizes the presentation, and runs the
term through the checked evaluator. The one-step engine is sound and, for base rewriting, complete. The
engine terminates under a measure and is confluent by Newman's lemma, with unique normal forms when the
usual termination and local-confluence hypotheses are supplied.

The shipped binary now exposes the path directly for a small editable dialect format with `sort`,
`term`, and `rewrite` declarations. The quick-test section near the top of this README shows the CLI
fixture, expected output, malformed-input behavior, a temporary custom dialect, the shell regression
gate, and the Lean test target.

AC equivalence is proved for binary-curried operators like rho's parallel `|`. The development gives a
verified total order on terms (`Order`), a canonical form that is sound, complete, and idempotent and so
decides AC-equivalence (`AC`), a modulo-AC engine sound for the `R/AC` relation (`ACEngine`), and
Church-Rosser modulo AC (`ACNormal`): AC-equivalent terms normalize to the identical term.

`ACMatch` adds the executable AC-aware matcher used by Cordial Miners. Its proved fragment is the linear
collection pattern with one fixed subpattern and one rest variable. That scope matches the protocol. Full
AC matching has hard cases even in small formulations, and variadic AC matching with sequence variables
needs a larger algorithm than the protocol uses. The scoped matcher follows Steven Eker's "Single
Elementary Associative-Commutative Matching" and Dundua, Kutsia, and Marin's "Variadic equational
matching in associative and commutative theories."

The core matcher theorems are `matchPatAC_acRest_witness`, `matchPatAC_acRest_sound`,
`matchPatAC_acRest_complete_of_flat_split`, `matchPatAC_acRest_complete_of_fresh_split`, and
`matchPatAC_sound`. The executable theorems `oneStepAC'_sound` and `evalAC'_sound` prove that the
AC-aware stepper and evaluator are sound for `RewStepModAC`. Full relation completeness for the whole
matcher remains a separate proof layer.

The type half has three layers. The grammar induces a head-sort discipline preserved by reduction
(`Sorts`, discharged on a concrete presentation in `SortSoundness`). Deeper, a recursive all-subterms sort
system (`WellSorted`) carries the substitution lemma both ways, the inst half (`inst_wellSorted`) and the
matching half (`SubjectReduction`), which combine into subject reduction for a contraction
(`subjectReduction_base`) and then lift through the one-step and many-step reduction relations
(`rewStep_preserves_wellSorted`, `rewStepMany_preserves_wellSorted`): every subterm keeps its declared sort
along reduction, shown on a variable-carrying rule.

`OSLF` is a machine-checked formalization of the first-order fragment of Stay and Meredith's
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
reducer, with monomorphization proved behavior-preserving. `MeTTaIL/Runtime/LanguageFile.lean` is the CLI
file parser for that path and covers the release format, not the full BNFC MeTTaIL surface. Everything is
axiom-clean (no `sorry`, the three standard axioms only). The remaining research items are listed in the
module headers and the proof-status appendix.

## Cordial Miners (PoR-weighted consensus)

`CordialMiners/` is a machine-checked formalization of PoR-weighted Cordial Miners, a leaderless
DAG-based BFT consensus protocol (arXiv 2205.09174). The layer follows the weighted Proof-of-Reputation
variant from a blueprint by Ben Goertzel. The layer is checked under the same bar as the rest of the
repo: 0 `sorry`/`admit`/`native_decide`/`partial`/`unsafe`, and the public theorem audits never report
`sorryAx`.

The headline theorem is `end_to_end_safety_of_finality_permanence`. Under a Byzantine-weight bound,
honest non-equivocation, and finality permanence, the protocol never finalizes conflicting values and
correct miners never publish conflicting positions. The ordering's prefix-monotonicity is derived, not
assumed. The proof goes through weighted-overlap arithmetic, threshold finality, blocklace closure,
equivocation detection, final-leader ratification, verified topological sorting, a coarse/fine
simulation, lossless extraction to MeTTaIL atoms, executable demos, and the runtime bridge below.

The reader-facing overview is [`CordialMiners/README.md`](CordialMiners/README.md). The book chapter
gives the explanation with the paper links.

```bash
lake build CordialMiners
```

The runtime bridge is the concrete "host a protocol as a MeTTaIL dialect" artifact. The bridge encodes Cordial
Miners facts and input events into `MeTTaIL.AST`, defines `cmPresentation` with the six coarse rewrite
rules, marks the state and inbox labels as AC, and runs the result with `evalAC'`.

```bash
lake build CordialMiners.Runtime.Run
```

Expected runtime checks:

```text
info: CordialMiners/Runtime/Run.lean:88:0: true
info: CordialMiners/Runtime/Run.lean:121:0: true
info: CordialMiners/Runtime/Run.lean:223:0: true
```

`CordialMiners/Runtime/Run.lean` also proves relation witnesses for the computed demo results:
`buriedProposal_eval_modAC`, `order_eval_modAC`, and `finality_eval_run_modAC`.

The main bridge theorem is in `CordialMiners/Runtime/Simulation.lean`:

```lean
trec_step_forward_decode :
  TrecState.Step s s' ->
  ∃ events target,
    RewStepModAC acOpCM cmPresentation (encConfig eW eH events s) target ∧
    astToState dW dH target = s'
```

The statement goes through `astToState` because runtime states are AC multisets and coarse states are
finite sets. Duplicate facts become decoded stutters. The backward theorem
`runtime_step_backward_of_decoders_acEq` says that a shaped runtime step, modulo AC, decodes either to one
coarse `TrecState.Step` or to the same coarse state, provided the field decoders respect `ACEq acOpCM`.
The executable Nat/Nat instance proves that condition as `dNat_acEq` and instantiates the theorem as
`runtime_step_backward_nat`. A theorem for arbitrary raw decoders is not claimed, because such decoders
can distinguish AC-equivalent payloads.

The transfer theorems are `trec_step_forward_reachable` and `trec_step_forward_wf`. The five-step run has
the concrete corollaries `finality_runtime_trec_reachable`, `finality_runtime_wf`, and
`finality_runtime_final_needs_propose`. The detailed theorem map and source notes are in
[`CordialMiners/Runtime/README.md`](CordialMiners/Runtime/README.md).

## Documentation

The book and a generated API reference are published together at
[mestto.github.io/LeaTTa](https://mestto.github.io/LeaTTa/):

- the book, a textbook-style treatment, at the site root;
- the API reference, every definition and theorem generated by doc-gen4, at
  [/api](https://mestto.github.io/LeaTTa/api/). References into Mathlib link to the official Mathlib
  documentation.

## The book

A textbook-style treatment of the formalization is in [`book/`](book/), built with Verso. The book covers
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

The interpreter ships as a single native binary, `LeaTTa`. The binary links only against the standard
C library, so a prebuilt release runs on any glibc Linux of the same architecture without installing
the Lean toolchain. Download an archive from the [releases page](https://github.com/MesTTo/LeaTTa/releases),
then:

```bash
tar xzf leatta-1.0.3-linux-x86_64.tar.gz
cd leatta-1.0.3-linux-x86_64 && ./install.sh   # installs to ~/.local/bin
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
self-described "hack" and several `TODO` notes at the points that decide evaluation. The
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
  `MeTTaILProofs` and `MeTTaILTests`) is the checked MeTTaIL formalization and runtime layer.
  `CordialMiners` is the PoR-weighted Cordial Miners consensus formalization, with its safety
  metatheory.
- Archived and not built: earlier exploratory models, including a four-register runtime, categorical
  metagraph rewriting, a Ruliad sketch, and an earlier approximate standard library. They live under
  [archive/](archive/) with their own README, kept for reference and not part of the verified work.
- In scope: the minimal interpreter, the standard library (computation, control, lists, sets,
  asserts), the runtime type system, mixed arithmetic, mutable spaces and state, conjunctive match,
  and the metatheory layer.
- Open: the full module system is not yet covered. The remaining MeTTaIL research targets are listed in
  the MeTTaIL section above and in the proof-status appendix.
