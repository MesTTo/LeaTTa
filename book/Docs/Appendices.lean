/-
LeaTTa: Appendices. Reference material consolidated into the book from the repository's former
standalone markdown files: proof status, coverage, and the comparison with Hyperon.
-/
import VersoManual
import Illuminate
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "Appendix: Proof Status, Coverage, and Improvements" =>
%%%
tag := "sec-appendices"
%%%

This appendix collects the reference material that used to live in separate files at the repository
root. It records exactly what is machine-checked, where each MeTTa and Hyperon topic is formalized,
and how the development compares with Hyperon's current implementation.

# Proof Status

The development separates three things that are easy to conflate: results checked by Lean in the
active build, earlier exploration kept under `archive/` but not compiled, and work that is planned
but not yet formalized.

## Machine-checked in the active build

Every theorem named here is checked by Lean's kernel in `MettaHyperonFull/Proofs/` or
`MettaHyperonFull/Operational/`, with no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe`.

 * *Determinism.* The abstract machine is a function; all nondeterminism is reified in the result
   list, not the transition relation: `interpretStack1_deterministic`, `interpretFuel_deterministic`,
   `mettaEval_deterministic` (`Proofs/Results.lean`).
 * *Confluence of the deterministic fragment*: `deterministic_confluent` (`Proofs/Confluence.lean`).
 * *First-argument indexing, sound and complete.* Head-symbol agreement is forced, so a rule that
   could fire is never hidden, and the index offers exactly the candidate rules:
   `matchAtoms_headKey` (`Proofs/Indexing.lean`), `candidates_sound` and `candidates_complete`
   (`Proofs/IndexingComplete.lean`).
 * *Type soundness.* The checker is permissive where MeTTa intends and reports `BadArgType` only on a
   real mismatch: `mettaEval_badArgType` (`Proofs/TypeSoundness.lean`); subject reduction over
   user-defined `=`-rewriting holds under its stated type-preserving-rule hypothesis:
   `reduction_preserves_type` (`Proofs/Preservation.lean`).
 * *Gradual consistency is not transitive*, for the relation and for the executable matcher:
   `not_consistent_distinct_syms` (`Proofs/Gradual.lean`).
 * *Alpha-equivalence* is an equivalence relation, preserves size, and coincides with `=` on closed
   atoms: `alphaEq_equivalence`, `AlphaEq.size_eq`, `alphaEq_iff_eq_of_closed` (`Proofs/Alpha.lean`).
 * *Substitution laws* used by binding propagation and preservation (`Proofs/Substitution.lean`).
 * *Operational semantics.* The four-register machine, append-only knowledge-base auditability, and
   gas non-creation (`Operational/Properties.lean`), with a bisimulation tying the indexed kernel to
   the published semantics at the level of rule firing: `kernel_mops_bisim`
   (`Proofs/Correspondence.lean`).

## Archived exploration, not part of the verified build

The following were modelled in an earlier, approximate form. They live under `archive/`, are not
compiled by the build, and must not be read as part of the verified development (see
`archive/README.md`). They are listed so the proof status is not mistaken for covering them.

 * Single-pushout and double-pushout graph rewriting, metagraph homomorphism, and the
   expression-to-DAG encoding (`archive/Metagraph/`).
 * Quotation and self-modification, trace history, and the Ruliad perspective (`archive/Reflection/`).
 * Host contracts and distributed-atomspace (DAS) matching (`archive/Interop/`).
 * Well-formedness metatheory over the earlier four-register runtime (`archive/MetaTheory/`,
   `archive/Runtime/`).

## Planned, not yet formalized

 * *Deeper preservation.* Thread the gradual consistency relation through the typing judgment in
   place of the current subtyping-top rule, and support polymorphic and dependent rules where the
   substitution threads through type arguments.
 * *Reflection.* Lift the fixed-signature assumption to a space-indexed judgment, for rules that
   rewrite `:` and `<:` facts themselves.
 * *Ruliad / topos layer.* Represented as a target interface only; the HoTT formalization is not
   done.

# Coverage

This section maps MeTTa and Hyperon topics to the files that formalize them. The runtime is a formal
reference: small enough to inspect and explicit about every host contract. It is not a drop-in
replacement for the Rust Hyperon runtime and does not cover the full Hyperon feature surface.

## Object language and matching

 * Single atom type, symbols, variables, grounded values, and nested expressions: `Core/Atom.lean`.
 * Grounding domain and grounded operations: `Core/Grounding.lean`, `Core/Builtins.lean`.
 * Pattern matching and unification: `Core/Matching.lean`, `Core/Unification.lean`.
 * Variable binding and substitution: `Core/Substitution.lean`, `Core/Bindings.lean`.
 * Alpha-equivalence: `Core/Alpha.lean`, `Proofs/Alpha.lean`.
 * Atomspaces as spaces of expressions, kept as bags (duplicates are significant): `Core/Space.lean`.

## Evaluation and the standard library

 * The minimal instruction set (`eval`, `chain`, `unify`, `cons-atom`, `function`/`return`, and so
   on): `Minimal/Interpreter.lean`.
 * Equality `(= L R)` as directed reduction and evaluation as an equality query:
   `Minimal/Interpreter.lean`, `Operational/Semantics.lean`.
 * First-argument rule indexing: `Minimal/Interpreter.lean` (`MinEnv.candidates`),
   `Proofs/IndexingComplete.lean`.
 * Nondeterminism (`superpose`, `collapse`), reified as a result list: `Minimal/Interpreter.lean`.
 * Control and list operations (`if`, `let`, `case`, `switch`, `map-atom`, `filter-atom`,
   `foldl-atom`) and set operations (`unique`, `union`, `intersection`, `subtraction`):
   `Minimal/Stdlib.lean`.
 * Expression manipulation and arithmetic over mixed integers and floats: `Core/Builtins.lean`,
   `Minimal/Stdlib.lean`.
 * Error handling (`Error`, `BadArgType`, the `assert*` family): `Core/Result.lean`,
   `Minimal/Stdlib.lean`.
 * Mutable spaces, state cells, and `import!` (the only IO): `Core/Space.lean`,
   `Minimal/Interpreter.lean`, `Minimal/Stdlib.lean`.

## Types

 * Type assignment `(: a T)` and the `Type` symbol: `Core/Types.lean`, `Minimal/Interpreter.lean`
   (`getTypes`).
 * Arrow types `(-> B A)` and function-application checking: `Core/Types.lean`,
   `Minimal/Interpreter.lean` (`typeCheckArgs`).
 * Gradual typing (`%Undefined%`, `Atom`, consistency): `Minimal/Interpreter.lean` (`matchType`),
   `Proofs/Gradual.lean`.

## Operational semantics and metatheory

 * The published four-register machine, barbed bisimulation, resource-bounded evaluation, and
   execution traces: `Operational/Semantics.lean`, `Operational/Bisimulation.lean`,
   `Operational/ResourceBounded.lean`, `Operational/Trace.lean`.
 * The metatheory results listed under Proof Status above: `Proofs/`.

## Runtime spine

The executable runtime parses atoms, stores ordinary atoms in the knowledge base, treats `!` forms
as evaluation requests, loads `(= L R)` rules, performs directional equality reduction by matching
`L` and instantiating `R`, implements `match`, `add-atom`, `remove-atom`, `get-atoms`, the atom and
math operations, and nondeterministic outputs, and returns result lists to model nondeterminism.
`Space.transform` (query then instantiate) is an internal helper used by `match`, not a separate
MeTTa operation; the `transform` step appears in the operational specification
(`Operational/Semantics.lean`), not as an instruction of the executable interpreter.

# Improvements over Hyperon

Hyperon's minimal MeTTa interpreter (`hyperon-experimental/lib/src/metta/interpreter.rs`) is, by its
authors' description, in an alpha state. Its source carries a self-described "hack" and several
`TODO` notes at the points that decide evaluation, and the written semantics is prose and pseudocode
without proofs. This development is a companion to that work: a total, machine-checked semantics that
agrees with Hyperon's own test oracle (270 of 270), replaces the mutable and ad-hoc machinery with
declarative constructs, and proves the properties the implementation only asserts.

## What is proved

The metatheory proves what the implementation asserts in comments. The full list with theorem names
is under Proof Status above; in short: determinism, confluence of the deterministic fragment, sound
and complete first-argument indexing, gradual-type permissiveness and faithful errors,
alpha-equivalence, and the kernel-to-specification bisimulation. A foundational choice is that
`Atom`'s `BEq` is hand-written and structural rather than derived, so it is kernel-reducible and the
indexing and type proofs go through; the derived instance compiles to opaque well-founded recursion
that blocks equational reasoning.

## Hyperon source markers and their treatment

The Hyperon sources carry explicit markers (`TODO`, hotfix, and "hack" comments) at points that
decide evaluation. Each is matched here by a declarative construct.

 * *The `is_evaluated()` mutable bit* (`interpreter.rs:1142`, commented "a hack") becomes static
   return-type gating: a function's result is inert iff its declared return type is `Atom`. No
   mutable bit, no reset-on-match.
 * *The `is_variable_op` hotfix* (`interpreter.rs:607`) becomes a total `isVariableHeaded` guard with
   type-directed argument evaluation.
 * *Tuple-versus-function dispatch decided twice* (`interpreter.rs:1430`, issues 235 and 458) is
   decided once from the operator's signature.
 * *`Rc<RefCell>` shared mutability for the stack and spaces* (issue 410, with related borrow panics)
   becomes a pure immutable `Stack`; one step is a total function, so that class of panic is
   impossible by construction.
 * *A global `make_unique` counter for freshening* becomes a pure gensym threaded through the
   interpreter (`freshenRule`).
 * *An unbounded interpreter loop* (`interpreter.rs:285`) becomes a total step with a fuel-bounded
   driver and a checked termination measure. MeTTa may legitimately diverge, so the bound is explicit
   rather than hidden.
 * *Fragile cross-call binding threading* (historically issues 127, 715, 290, 530, 911, since fixed)
   becomes evaluation as a pure, total, nondeterministic state transformer with continuation-scoped
   retention and transitive solution resolution.
 * *Stubbed alpha-equivalence* becomes real alpha-equivalence by canonical renaming, proved to be an
   equivalence relation.
 * *`Space::visit` undercounting same-head atoms* (issues 1079 and 1076, open) becomes explicit
   first-argument indexing, proved sound: no firing rule is dropped, and query completeness is a
   theorem rather than an empirically tested expectation.

## Status against the oracle

Hyperon's own unmodified tests run through this interpreter (`scripts/run-oracle.sh`) and pass 270 of
270 across 22 files, on the minimal interpreter rather than a curated subset. The passing set
includes the full dependent-type tier (`d1` through `d5`): GADTs, higher-order functions, dependent
length arithmetic, types as propositions, and auto type-checking with `BadArgType`, along with the
documentation operators `get-doc` and `help!`.

One file is left out: `f1_imports.metta`. Its authors mark it Python-mode-only, because it assumes
`&self` starts nearly empty with `corelib` and `stdlib` as separate importable modules, while this
build ships the prelude inside `&self`. The module machinery it would exercise, `import!` into named
spaces and diamond-dependency deduplication, is covered by `c2_spaces` (25/25) and `g1_docs` (10/10).
The corpus is vendored under `tests/corpus/` (MIT, commit `3f76dc4`), so the oracle reproduces 270/270
from a clean clone and fails the build on any divergence.
