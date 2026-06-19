/-
LeaTTa: Chapter: The Minimal Interpreter.
-/
import VersoManual
import Illuminate
import Docs.Cd
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Illuminate
open Docs

set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

#doc (Manual) "The Minimal Interpreter and Its Standard Library" =>
%%%
tag := "sec-interpreter"
%%%

MeTTa is defined in two layers, and LeaTTa follows that structure faithfully. At the bottom is
*minimal MeTTa*: a small "assembly language" of a dozen instructions in which the whole evaluator is
written. On top sits the standard library, itself written in MeTTa over those instructions, exactly
as in Hyperon. LeaTTa's interpreter (`Minimal/Interpreter.lean`) is the assembly evaluator; its
standard library (`Minimal/Stdlib.lean`) is the MeTTa-level prelude.

# The Instruction Set

The minimal instruction set is the irreducible core that everything else compiles to:

 * `eval` / `evalc`: one step of evaluation (querying the knowledge base for a matching `(= lhs rhs)`
   rule, or executing a grounded operation);
 * `chain`: evaluate an atom, then substitute its result into a template (this is how the
   normal-order core expresses *applicative* evaluation);
 * `unify`: conditional matching: `(unify a pat then else)`;
 * `cons-atom` / `decons-atom`: build and take apart expressions;
 * `function` / `return`: delimit an evaluation that runs to a `return`;
 * `collapse-bind` / `superpose-bind`: reify and re-inject the non-deterministic result set;
 * `metta`: full type-directed evaluation; `context-space`: the ambient atomspace; `capture`:
   freeze the current non-deterministic context.

Each instruction is a *total* function: there is no `partial`, and recursion is fuel-bounded with a
provably decreasing measure. When fuel is exhausted the evaluator does not silently truncate; it
emits MeTTa's `StackOverflow` error, so an exhausted run is always distinguishable from a genuine
result. This matters for replayability ({ref "sec-why"}[the blockchain motivation]).

# Evaluation Order

MeTTa is *applicative* at the surface, since arguments are evaluated before a function is applied,
but the minimal core is *normal-order*: instructions never evaluate their arguments implicitly. The
applicative behaviour is recovered by the type-directed `metta` loop, which emits `chain`
instructions to evaluate each argument whose declared type is not the meta-type `Atom`. Marking a
parameter `Atom` is therefore how a MeTTa function takes an argument *unevaluated* (quoted), which is
what `quote`, `if`, and the matching combinators rely on.

```diagram (cssWidth := "26em")
cd do
  let src ← CDM.node "surface MeTTa" cdInk
  let mid ← CDM.node "minimal MeTTa" cdInk
  let res ← CDM.node "result set" cdGreen
  CDM.grid #[#[some src], #[some mid], #[some res]]
  CDM.arrow src mid (some "type-directed metta") cdBlue .right
  CDM.arrow mid res (some "eval, query, grounded ops") cdBlue .right
```

# Non-Determinism, Reified

A MeTTa expression can reduce to *several* results; every matching equation fires. LeaTTa keeps this
non-determinism in an explicit result `List`, never in the transition relation: one step maps a
configuration to a *list* of successor configurations. This is the design choice that makes the
machine a deterministic function (see {ref "sec-meta"}[the metatheory chapter]) while still modelling
MeTTa's branching faithfully; `superpose` injects alternatives, `collapse` gathers them.

# Validation: the Hyperon Oracle

A specification is only as trustworthy as its agreement with reality. LeaTTa's interpreter is run
against Hyperon's *own* vendored test corpus on every build: *270 / 270* assertions pass across the
standard-library and chaining test files. These tests exercise the standard library across the board:
`if`, `let`/`let*`, `case`, `switch`, `collapse`/`superpose`, the `assertEqual*` family, the
list-surgery and arithmetic operations, the `*-math` functions, the type-checking helpers
(`type-cast`, `is-function`, `match-types`), and the space, state, and module operations. Agreement
with the reference implementation is the empirical anchor beneath the proofs of the following chapters.
