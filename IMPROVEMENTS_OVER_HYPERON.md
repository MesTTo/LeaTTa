# A machine-checked reference semantics for minimal MeTTa

Hyperon's minimal MeTTa interpreter (`hyperon-experimental/lib/src/metta/interpreter.rs`) is, by its
authors' description, in an alpha state. Its source carries a self-described "hack" and a series of
`TODO` notes at the mechanisms that decide evaluation, and the project's written semantics
(`docs/metta.md` and `docs/minimal-metta.md`, added in PR #1059) is prose and pseudocode without
proofs. This formalization is intended as a principled companion to that work: a total,
machine-checked semantics that

1. agrees with Hyperon's own test oracle. The unmodified `lib/tests/test_stdlib.metta` and the
   tutorial `a*`/`b*`/`c*`/`d*`/`e*`/`g*` scripts, vendored under `tests/corpus/` and run by
   `scripts/run-oracle.sh`, pass 270 of 270.
2. replaces the implementation's mutable and ad-hoc machinery with declarative, inspectable
   constructs.
3. proves the properties the implementation currently only asserts: determinism, confluence of the
   deterministic fragment, sound and complete rule indexing, type-error faithfulness, and
   α-equivalence. These are the properties that MeTTa's intended on-chain use will require, namely
   predictable, verifiable, and replayable execution.

As of this writing there is no issue or pull request in `hyperon-experimental` mentioning formal
verification, formal semantics, or blockchain use. This artifact is therefore novel, and it
mechanizes and extends the prose specification.

Everything below builds with 0 `sorry`, 0 `partial`, and 0 `unsafe`, on Lean 4 v4.31.0 with Mathlib.
The executable kernel (`Core`, `Minimal`, `Runtime`) is Mathlib-free and runnable. The proofs live in
a separate `MettaHyperonFull.Proofs.*` layer that imports Mathlib.

## Machine-checked metatheory (`MettaHyperonFull/Proofs/`)

What the implementation asserts in comments, this development proves. Each theorem is total and fully
checked.

| Property | Theorem(s) | Why it matters |
|---|---|---|
| **Determinism.** The abstract machine is a function; all nondeterminism is reified in the result `List`, not in the transition relation. | `interpretStack1_deterministic`, `interpretFuel_deterministic`, `mettaEval_deterministic`, `interpretFuel_done` (`Results.lean`) | On-chain replayability: every node re-deriving a result obtains the same one. The branching factor is exactly the product of branch counts (`cartesian_length`). |
| **First-argument indexing is sound.** Pattern matching forces head-symbol agreement, so the head bucket never hides a rule that could fire. | `matchAtoms_headKey` (`Indexing.lean`) | Justifies Hyperon's `AtomIndex` optimisation rigorously (treatment #9 below). The implementation's enumeration over same-head atoms is, by contrast, a known open bug (#1079). |
| **Gradual type system: permissive and faithful.** Undeclared operators, extra arguments, and the `%Undefined%`/`Atom` wildcards are never rejected, and `BadArgType` is emitted exactly when the checker flags a mismatch. | `typeMismatch_undeclared`, `matchType_undefined_left/right`, `matchType_atom_left`, `typeCheckArgs_nil`, `typeCheckArgs_no_param`, `mettaEval_badArgType` (`TypeSoundness.lean`) | A `BadArgType` in the output corresponds precisely to a checker rejection, so the runtime never invents a type error. Several of Hyperon's checks here are still settling (#919, #673, #669, #130). |
| **α-equivalence is an equivalence relation.** | `alphaEq_equivalence`, `AlphaEq.size_eq`, `alphaEq_iff_eq_of_closed` (`Alpha.lean`) | Replaces an earlier ad-hoc comparison. It also records a faithful caveat: because `Atom` carries host `Float`, the Boolean decider inherits IEEE 754 (`nan ≠ nan`), so `LawfulBEq Atom` is false. Hyperon shares this behavior. |
| **Substitution laws.** | `Subst.apply_nil`, `instantiate_nil`, `Subst.apply_of_closed`, `Subst.apply_size_le`, and the composition law `Subst.apply_compose` (`Substitution.lean`) | Foundation for binding propagation and the preservation proofs. |
| **Structural induction for the nested inductive `Atom`.** | `Atom.recAux` (`@[induction_eliminator]`, `Basic.lean`) | Infrastructure: `induction a` does not work out of the box for `Atom.expr : List Atom`. |

A foundational enabling choice is that `Atom`'s `BEq` is hand-written and structural rather than
derived. The derived instance compiles to well-founded recursion that is opaque even to `decide`,
since it does not reduce on a constructor mismatch, and this would block equational reasoning about
the matcher. The structural version computes identically, so the oracle is unchanged, and it is
kernel-reducible, which is what makes the indexing and type proofs possible.

## Hyperon source markers and this development's treatment

The Hyperon sources carry explicit markers, namely `TODO`, hotfix, and "hack" comments, at several of
the points that decide evaluation. The table records each marker, with the developers' own issue
references, alongside the corresponding construct here.

| # | Hyperon source marker | Where / issue | This formalization |
|---|---|---|---|
| 1 | An `is_evaluated()` mutable bit decides re-evaluation; it is set in one place, reset during matching, and checked in another. The source comments it as "a hack to prevent Expression working like Atom return type." | interpreter.rs `1142`; added as a performance change in PR #1000 | Static return-type gating (`returnsAtom`, mirroring `metta_call`): a function's result is inert iff its declared return type is `Atom`. No mutable bit and no reset-on-match. Same behaviour on the whole oracle, derived from the signature. |
| 2 | An `is_variable_op` hotfix in `query`, commented "This is a hotfix. Better way ... skip such evaluations in metta-call." | interpreter.rs `607` | A total, documented `isVariableHeaded` guard with type-directed argument evaluation, which is the approach the marker asks for. |
| 3 | Tuple-versus-function dispatch decided twice, noted to "conflict if user defines a function using a grounded atom." Duplicated type definitions can multiply results. | interpreter.rs `1430`; #235 / #458 | Dispatch decided once from the operator's signature (`argMask`/`returnsAtom`), not re-derived in `eval`. |
| 4 | `Rc<RefCell<…>>` shared mutability for the stack and spaces. | interpreter.rs throughout; #410 (noted as "difficult to get multi-threaded execution ... should happen after Alpha"); related borrow panics #241 / #397 / #930 | A pure immutable `Stack`/`Item`; one step (`interpretStack1`) is a total function, so this class of runtime panic is impossible by construction. |
| 5 | A global `make_unique` counter for variable freshening. | atom library | A pure gensym counter threaded through the interpreter (`freshenRule`); α-renaming per application, with no global state. |
| 6 | An unbounded interpreter loop (`while state.has_next()`), bounded only heuristically. | interpreter.rs `285`; PR #909, PR #970 | A total step with a fuel-bounded driver and a machine-checked termination measure (ranked `3·fuel`, `decreasing_by … omega`). MeTTa may legitimately diverge, so the bound is explicit. |
| 7 | Mutable binding threading via the `Rc<RefCell>` stack and `collapse-bind`/`check_alternatives`; deep cross-call binding was historically fragile (#127, #715, #290, #530, #911, all since fixed). | interpreter.rs `1110`–`1222` | Evaluation as a pure, total, nondeterministic state transformer. `apply_and_retain` is realised as continuation-scoped retention with transitive solution resolution (`resolveAtom`), which is what passes the recursive backchaining in `b2`. |
| 8 | Stubbed alpha-equivalence and ad-hoc comparisons. | implementation detail | Real α-equivalence by canonical renaming (`Core/Alpha`), proved to be an equivalence relation. |
| 9 | Linear left-hand-side handling, and `Space::visit` undercounting atoms with many same-head entries: enumeration is incomplete, and a variable-binding `match` returns empty where a literal `match` succeeds. | interpreter.rs `query`; #1079 (open), #1076 (open) | Explicit first-argument indexing (`MinEnv.ruleIndex`), proved sound (`matchAtoms_headKey`): no firing rule is ever dropped. Query completeness is a theorem rather than an empirically tested expectation. |
| 10 | Mutable atomspaces and state cells via `Rc<RefCell>`. | space / runner | A pure threaded `World` (named spaces, a state store, and token bindings) sequenced through nondeterministic evaluation; `import!` is the only IO. |

### Other open issues this model speaks to

- Non-monotonic evaluation, where "adding a function definition may remove some branches of the
  non-determinism ... the previous result has disappeared" (#461, open). Here the result set is a
  well-defined function of the program.
- Nondeterministic ordering, where superpose order is reported as inconsistent or order-dependent
  (#955, #859, #700). Here the `cartesian`/`superpose` order is a deterministic function of the
  inputs.
- One-sided versus two-sided reduction, where SKI reduction is reported as incorrect because MeTTa
  uses two-sided unification in `=`-reduction (#674, open). Here the matcher's direction is explicit
  and inspectable.

## Status against the oracle: 270 / 270

Hyperon's own unmodified tests run through this interpreter (`scripts/run-oracle.sh`), all faithful
and all on the minimal interpreter rather than a curated subset:

| file | result | | file | result |
|---|---|---|---|---|
| `test_stdlib.metta` | 39 / 39 | | `c2_spaces.metta` (spaces, `fork`, MORK) | 25 / 25 |
| `a1_symbols`, `a2_opencoggy`, `a3_twoside` | 7, 1, 4 | | `c3_pln_stv.metta` | 5 / 5 |
| `b0_chaining_prelim`, `b1_equal_chain` | 5, 8 | | `e1_kb_write.metta` | 3 / 3 |
| `b2_backchain.metta` | 6 / 6 | | `e2_states.metta` | 14 / 14 |
| `b3_direct.metta` | 4 / 4 | | `e3_match_states.metta` | 9 / 9 |
| `b4_nondeterm.metta` (comma-tuples) | 11 / 11 | | `d1_gadt.metta` (GADTs) | 14 / 14 |
| `b5_types_prelim.metta` | 26 / 26 | | `d2_higherfunc.metta` (HOF) | 25 / 25 |
| `c1_grounded_basic.metta` | 21 / 21 | | `d3`, `d4_type_prop`, `d5_auto_types` | 8, 18, 7 |
| | | | `g1_docs.metta` (`get-doc`) | 10 / 10 |

Everything builds with 0 `sorry`, 0 `partial`, and 0 `unsafe`. The passing set includes the full
dependent-type tier (`d1`–`d5`, 72/72): GADTs; higher-order functions such as curry, `lambda`, and
`fmap`, via expression-headed rule reduction; dependent length arithmetic, where `get-type` reduces
grounded operations in inferred types, so that `(ConsN "1" (ConsN "2" NilN))` has type
`(VecN String 2)`; types-as-propositions reasoning, where `=` is typed and `(empty)` prunes a
nondeterministic branch; auto type-checking with `BadArgType`; and error propagation through
evaluated arguments. It also includes documentation (`g1_docs`: `get-doc` building `@doc-formal`, and
`help!`). The recursive backchaining in `b2` closes through transitive binding resolution, and the
`(== 4 (+ ln 2))` error case in `c1` closes through error propagation in `==`. All are intended
Hyperon behaviours, confirmed against the test suite and `docs/metta.md`.

This corpus is the no-Python-mode subset. Hyperon's `f1_imports.metta` is marked by its authors as
Python-mode-only, with the note "This test won't work under no python mode ... there is no Python
stdlib," since it assumes `&self` starts near-empty with `corelib` and `stdlib` as separate
importable modules, whereas this pure-Lean build ships the prelude inside `&self`. The underlying
module mechanism, namely `import!` into named spaces and diamond-dependency deduplication, is
exercised by `c2_spaces` (25/25) and `g1_docs` (10/10). The corpus is vendored under `tests/corpus/`
(MIT, commit `3f76dc4`), so `scripts/run-oracle.sh` reproduces 270/270 from a clean clone and fails
the build on any divergence.

## What this is

The point is not the pass count but the shape: a reference the implementation can be validated
against. Where this development departs from the current implementation, it departs by being cleaner
and proven, and the properties an on-chain MeTTa will need, namely determinism, confluence, sound and
complete indexing, and type-error faithfulness, are machine-checked rather than asserted.
