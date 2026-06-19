# Formalizing MeTTaIL in Lean 4

A specification for a faithful Lean 4 formalization of F1R3FLY-io's MeTTaIL, built into the
LeaTTa repository alongside the existing MeTTa kernel, operational semantics, and metatheory.

Status: draft for review. Nothing here is pushed remotely. Work happens on the local branch
`mettail-formalization`.


## 0. Summary

MeTTaIL is F1R3FLY-io's intermediate language for MeTTa. You write a model of computation as a
*presentation* (a grammar of terms, equations that identify terms, and rewrite rules), and the tool
elaborates that presentation and can lift it from an untyped calculus to a typed one. The input is a
presentation of a graph-structured lambda theory (GSLT); the output is the concrete grammar of the
calculus it presents.

This document specifies what we formalize in Lean, to what depth, how it is laid out in the repo,
and how it connects to the existing development. It separates three things that the research made
clear are not the same:

1. what the Scala tool actually implements and tests (the determinate core),
2. what the design notes (`transformation.md`, `hypercube.md`) describe but only partly implement
   (the typed/modal layer),
3. what the two papers (`mq-calculus`, `present-moment`) add as research calculi.

The plan formalizes (1) completely and rigorously, formalizes the determinate part of (2) and flags
the open parts exactly as the source flags them, and treats (3) as scoped extensions with two
genuinely novel proof targets.


## 1. What MeTTaIL is

MeTTaIL = "Meta Type Talk Intermediate Language" (the README spelling). The GitHub one-line
description says "MeTTa Intermediate Language"; both are consistent because MeTTa itself expands to
Meta Type Talk. Author org: F1R3FLY-io (Lucius Gregory Meredith, the RChain/Rholang founder, and
Mike Stay). The repository we target is `github.com/F1R3FLY-io/MeTTaIL`, cloned locally at
`~/Dev/MeTTaIL` (branch `dev`).

MeTTaIL is a meta-language. A `.module` file is a program in an algebra of theory presentations.
Running the tool on a module parses it, elaborates a chosen theory instance into an in-memory
presentation, and emits a new grammar for the object calculus that presentation describes. So the
tool turns a modular, composable description of a calculus into the concrete syntax, equations, and
rewrites of that calculus.

A presentation of a GSLT (from `transformation.md`) is a presentation of an omega-order multisorted
algebraic theory (a "lambda theory" in the sense of Arkor and McDermott) with:

- a set `S` of generating shapes (sorts),
- a set `F` of function symbols, each with an input arity (an expression over `S` closed under
  products and exponentials) and an output arity (a bare shape in `S`),
- a set `E` of equations,
- two distinguished shapes `P` (processes) and `R` (reductions), and two distinguished function
  symbols `src : R -> P` and `tgt : R -> P` that give each reduction a formal source and target.

The presentation then adds equations setting each formal source and target equal to the "actual"
source and target supplied by other function symbols. That is how a GSLT records the operational
semantics of a calculus: a rewrite is an element of shape `R`, and `src`/`tgt` read off the redex
and the contractum.

There is a second, active repository, `F1R3FLY-io/mettail-rust`, a Rust rewrite (a `language!`
proc-macro generating LALRPOP parsers, `moniker` binding, and an Ascent/Datalog rewrite engine). We
do not target it. Its design notes are useful context: F1R3FLY frames GSLTs through a *syntactic
category* (morphisms preserve term structure) and a *semantic category* (morphisms preserve
bisimulation), linked by a forgetful functor and by OSLF (Operational Semantics in Logical Form),
and they state that the full-abstraction question has "the same shape as the rho calculus full
abstraction work being formalized in Lean." A Lean formalization of MeTTaIL therefore sits on
F1R3FLY's own roadmap.


## 2. Implemented vs. designed vs. in-papers

This separation drives every scope decision below.

### 2.1 Implemented and tested (Scala core)

The data model, the theory-instance algebra, the elaboration interpreter, binder desugaring, the
type-lifting transformation (symbol generation only), and grammar monomorphization. All have
ScalaTest specs, including a pinned elaboration of `Rholang.module`. This is the determinate heart.

### 2.2 Designed but only partly implemented (design notes)

`transformation.md` and `hypercube.md` describe the full untyped-to-typed transformation: the
type-lifted function symbols, the modal possibility types (`ctxrecv/ctxcomm/ctxsend/ctxposs`, the
`<>` modality), and a typing system ("the hypercube") with `type^T`/`kind^T` axioms, Start,
Weakening, an arrow type, per-constructor structural and term rules, and conv-like modal rules.

The code implements the symbol-generation core (type-lifting plus the duplicated-variable
extension). The modal-type generation is present in the notes but commented out in the code, and the
inference-rule layer (the typing judgment itself) is not coded. The notes themselves flag open
points: the modal naming is admitted to be ad hoc ("should choose names based on subtree location"),
one superscript assignment is annotated `// Is s1 s2 s1 correct?`, the recovery of ordinary arrow
types from the modal types is left open, and the cut-like rules are future work. Crucially, the
notes state the type system is "Not dependent product! This is just a lambda theory" and "the types
aren't dependent", so the typing judgment is multisorted simply-typed, not a dependent type theory.

### 2.3 In the papers (research calculi)

`papers/mqcalc/mq-calculus.tex` (Stay and Meredith): a process calculus where communication is
measurement, with a Born-rule COMM rule and complex amplitudes. `papers/agents/present-moment.tex`
(Meredith): the "spice" calculus, a rho-calculus whose COMM rule does bounded n-step lookahead
(`Q --n--> {Q1,...,Qm}`), grounding via `Q --0--> Q`. Neither paper states theorems; the spice
rule's well-foundedness is asserted, not proved. The Rust backends (`MeTTaIL2Matrix`,
`MeTTaIL-Gillespie`) are a GPU scheduler and a stochastic/quantum simulator; they are peripheral to
the semantics and out of scope except as reference for the mq-calculus rates.


## 3. The formalization target

All names below mirror the Scala data model so the Lean types are recognizably the same objects.

### 3.1 Data model

The object syntax of presentations:

- `Cat` (sorts / arities): `idCat (name : String) | listOf (c : Cat) | arrow (a b : Cat) | prod (cs : List Cat)`.
  This is the arity language: shapes closed under lists, exponentials, and products.
- `Item` (how a function symbol's arity is written in a rule):
  `terminal (s : String) | nterminal (c : Cat) | absNTerminal (x : String) (it : Item) | bindNTerminal (x : String) (c : Cat)`.
  Terminals are concrete-syntax literals; `nterminal` is a sort argument; the `absNTerminal`/
  `bindNTerminal` pair encodes a higher-order (exponential) argument with a bound variable.
- `Label`: `id (name : String) | wild | listE (c : Cat) | listCons (c : Cat) | listOne (c : Cat)`.
- `Rule` (a function symbol): `label : Label`, `cat : Cat` (output arity), `items : List Item`.
- `AST` (terms): `var (path : DottedPath) | sexp (label : Label) (args : List AST) | subst (body repl : AST) (v : DottedPath)`.
  `subst` is a built-in capture-avoiding substitution, the engine of the COMM rule.
- `Equation`: `impl (lhs rhs : AST) | fresh (x y : String) (e : Equation)` (the freshness guard
  `if x # y then ...`).
- `Rewrite`: `base (lhs rhs : AST) | ctx (h : Hyp) (r : Rewrite)`, with `Hyp` a premise
  `src ~> tgt` over dotted paths; a named rewrite is `RewriteDecl (name : String) (r : Rewrite)`.
- `Presentation` (the in-memory `BasePres`): `exports : List Cat`, `terms : List Rule`,
  `equations : List Equation`, `rewrites : List RewriteDecl`, `references : List (String x Presentation)`.

### 3.2 The theory-instance algebra and elaboration

`TheoryInst` is the expression language whose evaluation produces a `Presentation`. The eleven forms
the interpreter actually handles:

`empty | ref (name) | rec (let x = e in e') | ctor (path) (args) | free (path) | addExports (e) (exports) | addReplacements (e) (repls) | addTerms (e) (grammar) | addEquations (e) (eqs) | addRewrites (e) (rws) | conj (a b) | disj (a b) | subtract (a b)`.

Elaboration is `elaborate : Env -> TheoryInst -> Except Error Presentation`, a deterministic
recursive function over an environment of name-to-presentation bindings. Its meaning, faithful to
`InstInterpreter`:

- `empty` is the empty presentation; `ref`/`rec`/`ctor`/`free` do binding, sharing, parameter
  application, and recursive free-instantiation of a parameterized theory's whole dependency tree.
- `addExports` adds or renames sorts (a rename propagates through defs, equations, and rewrites).
- `addTerms`/`addEquations`/`addRewrites` extend a presentation, each with full well-formedness
  checks (see 3.3 invariants).
- `addReplacements` relabels a symbol, gives it new syntax, applies an argument permutation, and
  propagates the relabel and permutation through every equation and rewrite.
- `disj` is union (with dedup), `conj` is intersection filtered to common sorts and labels,
  `subtract` is difference that drops defs mentioning removed sorts.

Each operation has a checker (returns an optional error) and a worker; `elaborate` is the checked
composition.

### 3.3 Well-formedness

A presentation is well-formed when: every category mentioned in a rule is a declared export; labels
are unique; both sides of each equation and each rewrite conclusion have the same category, where a
bare variable unifies with any category; every variable on a rewrite's right-hand side or in a
premise also occurs on the left; freshness guards and dotted-path prefixes are respected;
replacement permutations are genuine permutations. These are the invariants the elaboration
preserves and the proofs are about.

### 3.4 Transformations

- `desugarBinds`: each rule with a `bindNTerminal` gains a `...ToArrow` companion whose higher-order
  argument is a single right-nested `arrow`.
- `typeLift` (the implemented `--hypercube`): for each function symbol add a `TypeLiftCC<L>DD`
  companion whose output is `T(cat)` and whose items are the lifted arguments, where the category
  functor is `T(idCat g) = idCat g`, `T(listOf a) = listOf (T a)`, `T(arrow a b) = prod [T a, arrow (T a) (T b)]`,
  `T(prod cs) = prod (cs.map T)`. Add extra parameters for variables that are duplicated in a base
  rewrite's left-hand side.
- `monomorphize`: replace arrow/product/list categories used in higher-order position by fresh named
  sorts and synthesize their `App`/`Lam`/`Ident`/`Make` constructor rules, producing a first-order
  grammar.

### 3.5 GSLT operational semantics

A presentation's rewrites induce a reduction relation on terms: a redex matches a rewrite's actual
source pattern, premises (`let src ~> tgt in ...`) drive congruence, and the contractum is the
actual target with `subst` applied. We define this relation and its single-step function over
`AST`, modulo the structural congruence given by `equations`. The flagship instance is the RHO
calculus (`Rholang.module`): COMM, par1/par2 congruence, replication, name restriction, and the
quote/drop reflection. Smaller instances are the lambda calculus and SKI from `hypercube.md`.

### 3.6 The hypercube typing (design layer)

The typing judgment `Gamma |- A : B` is an inductive relation (a span: `A : B` is read "a way that
A relates to B"). We formalize the determinate rules: Start, Weakening, the `type^T`/`kind^T`
axioms, the arrow type (simple, not dependent), and the per-constructor structural-type and term
rules for the instantiated calculi. The modal possibility types and the arrow-type recovery are
formalized as far as the source determines them, with the open points flagged in code comments that
quote the source's own annotations.

### 3.7 The papers' calculi (extensions)

- Spice calculus (`present-moment`): the n-step reachable-set relation `Q --n--> S` and the modified
  COMM rule, plus the `surf`/`int`/`PM` (present moment) definitions.
- mq-calculus: the Born-rule COMM transition and the `p (P | Q) = p P | p Q` hypothesis. This needs
  real and complex numbers, so it is noncomputable and lives only in the proof layer.


## 4. Layered plan and theorems

Four layers, each a set of Lean modules with stated theorems. Layers 1 to 3 are computable and
Mathlib-free, mirroring LeaTTa's kernel/proof split. Layer 4 (and the mq-calculus) use Mathlib and
live in a proof-only library.

### Layer 1: data model, presentation algebra, elaboration

Modules: `MeTTaIL/Syntax/*` (the data model), `MeTTaIL/Theory/Instance.lean`,
`MeTTaIL/Theory/WellFormed.lean`, `MeTTaIL/Theory/Elaborate.lean`.

Theorems:
- `elaborate` is total (terminates) and deterministic.
- Coherence: the checker rejects exactly the inputs on which the worker would be ill-formed
  (`check = none` iff `elaborate = ok`).
- Well-formedness preservation: each algebra operation maps well-formed presentations to well-formed
  presentations.
- Lattice laws of the presentation algebra: `disj` commutative, associative, idempotent up to dedup;
  `empty` a unit; the expected `conj`/`subtract` identities on components.
- Rename and replacement soundness: consistent renaming preserves well-formedness; a replacement's
  permutation is valid and is applied everywhere.

Faithfulness check (oracle): encode `Rholang.module`'s theory instance as a Lean `TheoryInst` and
prove `elaborate` yields the `Presentation` pinned by the Scala `InstInterpreterSpec`. This is a
machine-checked cross-test against the real tool without needing a `.cf` parser. A full surface
parser is optional future work.

### Layer 2: transformations

Modules: `MeTTaIL/Transform/Desugar.lean`, `MeTTaIL/Transform/TypeLift.lean`,
`MeTTaIL/Transform/Monomorphize.lean`.

Theorems:
- `T : Cat -> Cat` total; the arity discipline is respected.
- `desugarBinds`, `typeLift`, and `monomorphize` each produce well-formed presentations.
- The `...ToArrow` companion has the right arrow arity; each `TypeLiftCC L DD` has output `T(cat)`.
- Monomorphization name-mangling is injective (distinct higher-order categories map to distinct
  sorts).

### Layer 3: GSLT operational semantics and instances

Modules: `MeTTaIL/Semantics/Reduce.lean`, `MeTTaIL/Semantics/Congruence.lean`,
`MeTTaIL/Calculi/Rho.lean`, `MeTTaIL/Calculi/Lambda.lean`, `MeTTaIL/Calculi/SKI.lean`,
`MeTTaIL/Bridge/Operational.lean`.

Theorems:
- The reduction relation is well-defined; structural congruence is an equivalence and is a
  congruence for the constructors.
- RHO: reflection iso laws hold; COMM produces well-formed contracta; a concrete reduction example
  computes. SKI: the six combinator rules reduce closed terms; head reduction is deterministic.
  Lambda: beta and head reduction, confluence of the deterministic fragment where tractable.
- Bridge: relate a GSLT reduction step to LeaTTa's `Operational` four-register machine where they
  align, or present MeTTa itself as a GSLT and connect to the kernel. Depth depends on the scope
  decision in section 7.

### Layer 4: typing, soundness, and the papers' calculi

Modules: `MeTTaIL/Typing/Hypercube.lean`, `MeTTaIL/Typing/Soundness.lean`,
`MeTTaIL/Extensions/Spice.lean`, `MeTTaIL/Extensions/MQCalculus.lean` (the last is Mathlib-backed,
proof-only).

Theorems:
- Typing is well-defined for RHO/lambda/SKI; the structural-type formation and term rules are
  consistent; subject reduction (preservation) for the determinate fragment. Open modal points are
  flagged, not faked.
- Spice: grounding (`Q --0--> {Q}`), `n = 0` recovers ordinary rho COMM, and well-foundedness of the
  modified COMM. The last is a genuine contribution; the source asserts it without proof.
- mq-calculus: the COMM-as-measurement transition; probability conservation (the Born weights sum to
  one); the parallel-distribution hypothesis as a definitional law; normalization and interference
  invariants.


## 5. Repository layout and LeaTTa integration

A new Lean library, a sibling of the existing `Metatheory` and `Operational` targets, so the runnable
`LeaTTa` binary never links it and CI machine-checks it on its own.

```
MeTTaIL/                         -- new top-level lean_lib, root `MeTTaIL`
  Syntax/                        -- Cat, Item, Label, Rule, AST, Equation, Rewrite, Presentation
  Theory/                        -- TheoryInst, WellFormed, Elaborate
  Transform/                     -- Desugar, TypeLift, Monomorphize
  Semantics/                     -- Reduce, Congruence
  Calculi/                       -- Rho, Lambda, SKI
  Typing/                        -- Hypercube, Soundness            (Layer 4)
  Extensions/                    -- Spice, MQCalculus               (Layer 4; MQCalculus is proof-only)
  Bridge/                        -- Operational (to MettaHyperonFull.Operational)
  Proofs/                        -- the Mathlib-backed proofs about Layers 1 to 3
```

`lakefile.lean` gains a computable `lean_lib MeTTaIL` (Mathlib-free, like the kernel) and a
`lean_lib MeTTaILProofs` (Mathlib-backed, like `Metatheory`). The split is the same computability
discipline LeaTTa already uses: the data model, elaboration, transformations, and reduction stay on
`List`/`Std.HashMap` so they run; the proofs and the mq-calculus use Mathlib.

Reuse from the existing development: `MettaHyperonFull.Core` already has atoms, substitution,
alpha-equivalence, and bag-valued spaces. Where the GSLT term language overlaps the MeTTa atom
language we share rather than duplicate. The `Bridge` connects the GSLT reduction relation to the
`Operational` four-register machine.

Quality invariants (inherited from LeaTTa, non-negotiable): zero `sorry`, zero `admit`, zero
`native_decide`, zero `partial`, zero `unsafe`. The existing `scripts/ci/check-no-forbidden.sh`
extends to the new library.


## 6. Faithfulness and honesty policy

- Lean names mirror the Scala constructs so the correspondence is auditable.
- We formalize what the source determines. Where the source is open (the modal naming, the
  `// Is s1 s2 s1 correct?` superscript, the arrow-type recovery, the cut-like rules, the asserted
  spice well-foundedness), we either prove it as a stated contribution or mark it precisely with a
  comment that quotes the source. We do not present an open design choice as settled, and we do not
  paper over a gap with an axiom or a `sorry`.
- Each calculus instance is checked by a computable reduction example where possible, the analogue of
  LeaTTa's oracle.


## 7. Scope and sequencing (your decisions)

The full landscape above is the exhaustive plan. Two choices are genuinely yours and steer where the
deepest proof effort goes and how far the first local milestones reach. They are recorded here once
you decide.

- Scope reach: Layers 1 to 3 (the implemented, determinate core: data model, elaboration,
  transformations, GSLT reduction with RHO/lambda/SKI) as the guaranteed-solid foundation; or also
  Layer 4 typing and soundness; or also the papers' calculi (spice well-foundedness, mq-calculus).
- Primary investment: which thread gets the deepest proofs first: the elaboration engine (what the
  tool computes), the type system and soundness (the verification and blockchain story), the
  operational-semantics bridge to LeaTTa (the "build off my setup" angle), or the novel calculi.

Decision (recorded 2026-06-20): full scope, including the papers' calculi. The deepest proof effort
is sequenced as: first the faithful tool model (the elaboration engine and the oracle cross-check),
then type soundness (the hypercube typing and subject reduction), then the novel calculi (spice
well-foundedness and the mq-calculus), and finally the bridge to LeaTTa's operational machine. The
build order remains Layer 1, then 2, then 3, then 4, committed locally in atomic pieces, nothing
pushed until you say so.
