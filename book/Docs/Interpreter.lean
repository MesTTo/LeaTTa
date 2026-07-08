-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

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

MeTTa is defined in two layers. At the bottom is *minimal MeTTa*: a small "assembly language" of
thirteen instructions that the whole evaluator is written in. On top sits the standard library,
itself written in MeTTa over those thirteen instructions, exactly as in Hyperon. LeaTTa's interpreter
(`Minimal/Interpreter.lean`) is the assembly evaluator; its standard library (`Minimal/Stdlib.lean`)
is the MeTTa-level prelude.

# The Instruction Set

The thirteen minimal instructions are the base layer that everything else compiles to. You can read
them as a tiny assembly language for MeTTa:

 * `eval` / `evalc`: one step of evaluation (querying the knowledge base for a matching `(= lhs rhs)`
   rule, or executing a grounded operation);
 * `chain`: evaluate an atom, then substitute its result into a template (this is how the
   normal-order core expresses *applicative* evaluation);
 * `unify`: conditional matching: `(unify a pat then else)`;
 * `cons-atom` / `decons-atom`: build and take apart expressions;
 * `function` / `return`: delimit an evaluation that runs to a `return`;
 * `collapse-bind` / `superpose-bind`: reify and re-inject the non-deterministic result set;
 * `metta`: full type-directed evaluation; `metta-thread`: evaluate an atom against a given space;
   `context-space`: the ambient atomspace; `capture`: freeze the current non-deterministic context.

Each instruction is a *total* function: there is no `partial`, and recursion is fuel-bounded with a
provably decreasing measure. When fuel runs out the evaluator does not silently truncate; it
emits MeTTa's `StackOverflow` error, so an exhausted run is always distinguishable from a genuine
result. That matters for replayability ({ref "sec-why"}[the blockchain motivation]).

# Evaluation Order

At the surface, MeTTa is *applicative*: arguments are evaluated before a function is applied. The
minimal core is *normal-order*, though: instructions never evaluate their arguments implicitly. The
applicative behaviour is recovered by the type-directed `metta` loop, which emits `chain`
instructions to evaluate each argument whose declared type is not the meta-type `Atom`. Marking a
parameter `Atom` is how a MeTTa function takes an argument *unevaluated* (quoted), which is
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

A MeTTa expression can reduce to *several* results because every matching equation fires. LeaTTa
keeps this non-determinism in an explicit result `List`, never in the transition relation: one step
maps a configuration to a *list* of successor configurations. That is the design choice that makes
the machine a deterministic function (see {ref "sec-meta"}[the metatheory chapter]) while still
modelling MeTTa's branching faithfully. `superpose` injects alternatives; `collapse` gathers them.

# Validation: the Hyperon Oracle

On every build, LeaTTa's interpreter is run against Hyperon's *own* vendored test corpus, and
*270 / 270* assertions pass across the standard-library and chaining test files. The tests cover:

 * control flow: `if`, `let`/`let*`, `case`, `switch`;
 * non-determinism: `collapse`/`superpose`;
 * the `assertEqual*` family;
 * list surgery and arithmetic;
 * the `*-math` functions;
 * the type-checking helpers: `type-cast`, `is-function`, `match-types`;
 * space, state, and module operations.

That agreement with the reference implementation is what grounds the proofs in the chapters that
follow.
