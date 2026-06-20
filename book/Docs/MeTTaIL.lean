/-
LeaTTa: Chapter: MeTTaIL, formalized.
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

#doc (Manual) "MeTTaIL: A Machine-Checked Meta-Language of Graph-Structured Lambda Theories" =>
%%%
tag := "sec-mettail"
%%%

MeTTaIL is F1R3FLY-io's intermediate language for MeTTa. Its full name is the Meta Type Talk
Intermediate Language, and it is the work of Lucius Gregory Meredith and Mike Stay, the people behind
the rho-calculus and the F1R3FLY blockchain. This chapter is about a second Lean development, built
alongside the MeTTa kernel of the rest of this book, that formalizes MeTTaIL and checks it against the
real tool.

The short version: MeTTaIL is a meta-language. You do not write a program in it, you write down a
*model of computation*, and the tool turns that description into the concrete syntax, equations, and
rewrite rules of the calculus you described. The description is a presentation of a graph-structured
lambda theory, a GSLT. We formalize the presentations, the algebra that builds them, the pipeline
that elaborates and transforms them, the reduction they induce, and the metatheory you would want of
all of it. As far as we can tell this is the first machine-checked formalization of MeTTaIL: the
F1R3FLY repositories named for this work (`OSLF`, Mike Stay's `GSLT`) are at present only READMEs.

# What a GSLT Presentation Is

A presentation of a graph-structured lambda theory has four parts:

 * a set of generating shapes (sorts);
 * a set of function symbols, each with an input arity (built from the shapes by products and
   exponentials) and an output arity (a shape);
 * a set of equations identifying terms;
 * two distinguished shapes `P` (processes) and `R` (reductions), with `src, tgt : R -> P` giving each
   reduction a source and a target.

The last part is what makes a GSLT describe an operational semantics. A rewrite is an element of
shape `R`, and `src` and `tgt` read off its redex and contractum. The RHO calculus, the lambda
calculus, SKI, and the Ambient calculus are all presented this way.

In Lean the object syntax is one data model, `MeTTaIL.Syntax`, mirroring the tool's `BasePres` and its
BNFC abstract syntax symbol for symbol: `Cat` for arities, `Rule` for function symbols, `AST` for
terms, `Equation`, `Rewrite`, and `Presentation`. We compare terms with a hand-written structural
`BEq`, exactly as the Scala interpreter compares with `.equals`, because Lean's `deriving` does not
support the inductives that nest through `List`.

# Elaboration, and Why We Trust It

A `.module` file is a program in an algebra of theory presentations. You start from `Empty`, extend a
presentation with sorts, symbols, equations, and rewrites, compose presentations with union,
intersection, and difference, and apply parameterized theories. The Lean `elaborate` function
interprets that algebra into a presentation. It is fuel-bounded, because applying a theory expands
another theory's body, and that keeps the development free of `partial`.

Here is the part worth dwelling on. We did not just write an elaborator and hope it matches MeTTaIL.
We built the real Scala tool and ran it, and then proved, by `decide` in the Lean kernel, that our
elaborator reproduces its output exactly. Take F1R3FLY's own `Rholang.module`, which builds the RHO
calculus from universal algebra (`EmptySet`, `Monoid`, `CommutativeMonoid`, then the process layers).
The tool prints an Interpreted Presentation with the sorts `Proc` and `Name`, eight constructors, ten
equations, and four rewrites. Our oracle states that elaborating the same module gives precisely that
presentation, and the kernel checks it. We deliberately use `decide`, which the kernel verifies,
rather than `native_decide`, which would trust the compiler.

The transformations are checked the same way. After elaboration the tool desugars binders, optionally
lifts the untyped calculus to a typed one (the lambda-cube-style `--hypercube` pass), and monomorphizes
higher-order categories into a first-order grammar. We formalize all three (`desugarBinds`, the
type-lift, `monomorphize`) and prove each reproduces the tool's printed output for the Rholang
example: the `...ToArrow` companions, the `TypeLiftCC..DD` companions with the duplicated-channel
extension, and the `ArrowCC..DD` sort with its application, lambda, and variable constructors.

# The Operational Semantics

A presentation's rewrites induce reduction on terms. The relation `Reduces` fires a rewrite when its
left-hand side matches a term, binding the pattern variables; each premise `src ~> tgt` requires the
bound `src` to itself reduce, binding `tgt`; the contractum is the right-hand side instantiated with
those bindings. Base rewrites contract a redex directly, premised rewrites are the congruence rules.
The executable matcher and the relation are tied together: every reduct the matcher produces is a
genuine reduction.

# Type Soundness and Confluence

The GSLT framework is generic, so we instantiate it and prove the metatheory you would expect for the
calculi that have a determinate typing.

 * SKI combinatory logic is binder-free, so its typing and reduction are first-order. We prove subject
   reduction and confluence (Church-Rosser, by Takahashi parallel reduction).
 * The simply-typed lambda calculus, in de Bruijn form, pays the substitution cost. We prove the
   weakening and substitution lemmas, then preservation and progress, then confluence of beta.

Every one of these is a real kernel-checked proof. An axiom audit shows the whole corpus depends only
on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`); several proofs use none
beyond `propext`. There is no `sorry`, `admit`, `native_decide`, `partial`, or `unsafe` anywhere in
the development, and a CI guard enforces that.

# Two Calculi from the Papers

F1R3FLY's recent papers add two calculi, and we formalize the core of each.

The present-moment paper gives the rho-calculus a "spice" rule: a modified COMM that does bounded
`n`-step lookahead, `Q --n--> {Q1, ..., Qm}`. The rule looks self-referential, because the reduction
it uses includes COMM itself, and the paper asserts, without proof, that it is well-founded. We
formalize the heart of it as bounded reachability over any one-step relation, defined by structural
recursion on the fuel `n`, and we prove the grounding `Q --0--> {Q}` that resolves the apparent
circularity. Our reachability function is total by construction (structural recursion on the fuel),
which is the termination guarantee the source asserts without proof. The full modified COMM rule over
an actual rho-calculus process type is not formalized here; we capture the reachability core it rests
on.

The mq-calculus paper builds a process calculus where communication is measurement. We formalize the
semantic core that makes its COMM rule well-defined: a finite quantum state is a normalized vector of
complex amplitudes, the Born probability of an outcome is the squared modulus of its amplitude, and
those probabilities form a genuine distribution (they are in the unit interval and sum to one). So
measurement-by-communication neither creates nor loses probability. We also record interference: the
Born probability of a superposition is not the classical sum.

# Connecting Back to the Kernel

This book's MeTTa kernel and the MeTTaIL framework meet in a bridge: an embedding of the kernel's
`Metta.Atom` (the four metatypes) into GSLT terms. A symbol becomes a nullary constructor, a variable
a GSLT variable, an expression a wild-labelled application, and a grounded atom a keyed nullary
constructor. The embedding is injective on the grounded-free fragment; grounded atoms inherit the same
IEEE-754 float caveat the kernel documents for its own equality. This is the precise sense in which
MeTTa is a GSLT object language.

The metatheory layer rounds this out: decidable equality and a lawful Boolean equality for the whole
data model, the pipeline invariants (each transformation touches only the term list), and the
presentation algebra's set laws (union, intersection, and difference behave as set operations on each
component).

# What Is Left Open, Honestly

The source itself leaves its deepest layer open. MeTTaIL's modal type system (the possibility
modalities and the recovery of arrow types in the design notes) is admitted there to be intuited
rather than finished, and the rho-calculus full-abstraction result it points at is work in progress.
We formalize the determinate fragments and flag the open parts in place rather than papering over
them. The Scala tool's own `--hypercube` pass omits the modal types too, and our type-lift matches the
tool, not the unfinished note. The per-variable category-consistency check of the elaborator's type
checker is the one piece of the tool we have left as future work; the category-match and
bound-variable checks are in place.

Building a faithful model is also a good way to find bugs in the thing you are modeling, and we found a
few in the tool's rename and checking code. Where the Scala does something wrong, an export rename that
overwrites every rule's output sort, a static check that only inspects the first export, a checker that
does not descend through `let`, the Lean does the correct thing and leaves a note at the divergence.
The five we found are written up for the F1R3FLY team in `MeTTaIL/HYPERON_IMPROVEMENTS.md`.
