/- jscpd:ignore-start -/
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
/- jscpd:ignore-end -/

MeTTaIL is F1R3FLY-io's intermediate language for MeTTa. Its full name is the Meta Type Talk
Intermediate Language, and it is the work of Lucius Gregory Meredith and Mike Stay, the people behind
the rho-calculus and the F1R3FLY blockchain. Here we formalize MeTTaIL alongside the MeTTa kernel and
check the result against the real tool.

The short version: MeTTaIL is a meta-language. You do not write a program in it, you write down a
*model of computation*, and the tool turns that description into the concrete syntax, equations, and
rewrite rules of the calculus you described. The description is a presentation of a graph-structured
lambda theory, a GSLT. We formalize the presentations, the algebra that builds them, the pipeline
that elaborates and transforms them, the reduction they induce, and the expected metatheory. I have not
found an earlier machine-checked formalization of MeTTaIL: the
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
interprets that algebra into a presentation. The elaborator is fuel-bounded, because applying a theory expands
another theory's body, and that keeps the development free of `partial`.

The trust point is concrete. We built the real Scala tool and ran it. Then we proved, by `decide` in the
Lean kernel, that the Lean elaborator reproduces its output exactly. Take F1R3FLY's own
`Rholang.module`, which builds the RHO
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

The shipped binary exposes the same idea for an editable runtime file. `MeTTaIL/Runtime/LanguageFile.lean`
parses a small external dialect format with `sort`, `term`, and `rewrite` declarations, elaborates it,
monomorphizes it, and runs a term with the generic reducer. For example, the checked fixture
`tests/mettail/bool.mettail` declares `tt`, `ff`, and `notOp`; running
`LeaTTa --mettail tests/mettail/bool.mettail --term '(notOp tt)'` prints `ff`. That file format is not
the full BNFC MeTTaIL surface. The format is the external runtime path for base-rewrite dialects, wired to the
same verified reducer.

# The Operational Semantics

A presentation's rewrites induce reduction on terms. The relation `Reduces` fires a rewrite when its
left-hand side matches a term, binding the pattern variables; each premise `src ~> tgt` requires the
bound `src` to itself reduce, binding `tgt`; the contractum is the right-hand side instantiated with
those bindings. Base rewrites contract a redex directly, premised rewrites are the congruence rules.
The executable matcher and the relation are tied together: every reduct the matcher produces is a
genuine reduction.

The conditional runtime bridge has two layers. `RuntimeCongruenceStep` is the broad runtime predicate:
it covers one-premise `sexp` argument congruence and both `Subst` context forms (`substB`, `substR`).
`SexpArgCongExtension` is the presentation-level predicate for premised rewrite declarations; it covers
the rules that a presentation can add syntactically, including the RHO `RNew` shape
`PNew[x, Src] -> PNew[x, Tgt]`. The bridge proves a `SexpArgCongExtension` extends the base runtime
only by `RuntimeCongruenceStep`s, then derives the confluence transport as a corollary. A top-level
`Subst` right-hand side is still not treated as a declaration-level `SexpArgCongRule`, because runtime
instantiation resolves `Subst` immediately with `subst1` rather than rebuilding the `Subst` node.

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

The proof architecture follows the checked runtime modules under `MeTTaIL/Semantics`,
`MeTTaIL/Runtime`, and `MeTTaILProofs`. Newman's lemma and the Knuth-Bendix-Huet critical-pair route
handle first-order confluence. The conditional fragment
uses the extended critical-pair obligations described in the conditional-rewriting literature, with
proper conditional critical pairs and conditional variable pairs supplied as hypotheses. The OSLF line
follows Stay and Meredith's distributive-law view of operational semantics {citep stayMeredithLogic}[]
and its enriched-Lawvere-theory companion {citep enrichedLawvereSemantics}[]. The general categorical
backbone is Beck's composite-monad theorem {citep beckDistributiveLaws}[], in the 2-categorical setting
made explicit by Street {citep streetFormalTheoryMonads}[]; `MeTTaILProofs/DistributiveLaw.lean`
formalizes that theorem for Mathlib monads.

# The Denotational Semantics Target

The newer F1R3FLY manuscripts add a denotational target for this operational story. The first paper
builds a red/black reflective set theory where each colour's atoms are the other colour's sets
{citep knottedUniverse}[]. The second paper uses that universe for the rho-calculus: quote and
dereference become colour-swap operations, rho terms denote RSpace-style tables, and the behavioural
model identifies equality with context bisimilarity {citep quotingColourSwap}[]. A follow-up RSpace
paper makes the store key polymorphic: keys can be paths, the store becomes a trie, and prefix
comparability changes what a cut matches without allowing ambient store reactions {citep pathsSubspaces}[].
The knotted-topoi paper then lifts the pattern one categorical level: a finitely presentable GSLT
presented in MeTTaIL should desugar to rho by installing persistent rewrite listeners at term locations,
then inherit the fully abstract rho denotation inside the knotted topos {citep knottedTopoi}[].

The compilation side has its own source trail. The MeTTa-calculus note describes the RSpace reading of
MeTTa-style spaces: comprehensions and outputs become keyed entries, parallel composition becomes RSpace
merge, and opposite-polarity entries at the same key react {citep mettaCalculus}[]. The Turing-to-rho
note shows the same rho core can host a Turing-machine encoding where tape cells are channels, reads are
for-comprehensions, writes are outputs, and step and namespace costs transport to rho reductions
{citep rhoViaTuring}[]. The optimal-channel paper gives the missing compiler-side target for a general
GSLT-to-rho translation: channel names should be computed from rewrite contexts by set-automaton partial
evaluation, so outer channels survive inner reductions {citep optimalChannels}[].

The Lean side now states that claim as an interface. `MeTTaIL.Semantics.Denotational` defines labelled
transition systems, simulations, bisimulations, the kernel relation of a denotation, and `FullyAbstract`,
the statement `denote s = denote t <-> Bisimilar lts s t`. The theorem `fullyAbstract_of_kernel` packages
the coalgebraic argument used by the papers: if equality in the behaviour object is exactly the
bisimulation kernel, the denotation is fully abstract. The packaged `FullyAbstractModel` also records the
context-congruence obligation, because the papers need context labels to make bisimilarity a congruence
without a later closure step.

The transfer theorem is there too. `fullyAbstract_of_bisimilarity_translation` says that a source calculus
inherits full abstraction from a target calculus when the translation preserves and reflects bisimilarity.
`congruence_of_bisimilarity_translation` adds the context side: if source contexts commute with target
contexts under the translation, target congruence pulls back to source congruence.
`FullyAbstractModel.pullback` packages those two facts as a constructor for the pulled-back model. These
theorems are the part of the knotted-topoi story that can already be stated before the missing
MeTTaIL-to-rho desugaring theorem is supplied.

`MeTTaIL.Semantics.Rho` starts the target side of that theorem. It defines rho names and processes,
quote/drop, ordinary and persistent send/receive COMM, structural congruence for parallel composition,
and a one-channel RSpace produce/consume boundary. The local implementation source is the
`mettatron-workspace` checkout:
`MeTTa-Compiler/src/pathmap_par_integration.rs` serializes MeTTa state into `Par`, while
`f1r3node/rholang/src/rust/interpreter/reduce.rs` runs `produce` and `consume` against RSpace using
`ListParWithRandom`, `BindPattern`, `TaggedContinuation`, and persistent flags. `eval_send` evaluates
and substitutes the send channel and data before calling `produce`, which is why the Lean bridge emits
the encoded contractum process rather than a suspended dereference.

The same repo also carries an older K semantics in `rholang/src/main/k/rholang/`. The relevant files are
`configuration.k`, `sending-receiving.k`, and `persistent-sending-receiving.k`. They split execution into
`<In>` and `<Out>` cell creation, candidate-ID bookkeeping, pattern matching, substitution, ordinary
send/receive, persistent send, persistent receive, and the persistent/persistent loop case.

`MeTTaIL.Semantics.RhoKMachine` now checks the four one-channel COMM cases from that K machine:
ordinary input with ordinary output, ordinary input with persistent output, persistent input with
ordinary output, and persistent input with persistent output. It defines K-style input and output cells
with IDs, candidate sets, and the local `ReadyPair` guard: `CandidatePair` from `<InData>` and
`<OutData>`, plus `MatchedOne` for the result of `aritymatch["STDMATCH"]` on the one-message payload.
It then proves that each branch reifies to rho COMM modulo parallel-structure laws. It also models the
one-pair creation rules that move a surface input or output into a K cell and record candidates from the
current global ID lists; those creation steps preserve the reified rho process by
`Rho.KMachine.creation_to_struct`. The branch theorems are `Rho.KMachine.ordinaryReceive_to_rho`,
`Rho.KMachine.persistentOutput_to_rho`, `Rho.KMachine.persistentReceive_to_rho`, and
`Rho.KMachine.persistentBoth_to_rho`. The file does not yet model full multi-cell ID maintenance, the
full K matcher, or the repeated scheduling discipline behind the persistent/persistent loop.

`MeTTaIL.Semantics.RhoCompiler` adds the first checked compiler bridge. It follows the direct-rule
shape in the `mettail-rust` GSLT2rho prototype: a rule has a persistent listener on a rule channel, and
the matcher sends the computed contractum as a packet. The theorem
`Rho.Compiler.applyBaseRewrite_reduces_and_emits` says that a successful `applyBaseRewrite` result is a
real MeTTaIL `Reduces` step and that the rho listener emits `encodeAST` of the contractum at the source
term location. The theorem is packet-level. The file also proves `Rho.Compiler.contractum_kstep`, so the
same packet exchange is a K-machine persistent-receive step whose `ReadyPair` proof comes from the
packet channel, and uses `Rho.KMachine.acceptAny` because `applyBaseRewrite` has already produced the
matched contractum. `Rho.Compiler.contractum_kstep_to_rho` says that K step reifies back to rho
reduction. It does not prove the full matcher/router, contextual channel compiler, binder freshness
discipline, or two-direction operational correspondence.

The path-key RSpace note adds another interface in the same Lean file. `PathRSpace.Path` is a list of
names, `PathRSpace.Prefix` and `PathRSpace.Comparable` state the prefix-order matching condition, and
`PathRSpace.SubspaceBranch` records the two COMM cases: output deeper than input, or input deeper than
output. The theorem `PathRSpace.comparable_iff_nonempty_subspaceBranch` checks that comparability is
exactly enough to choose one of those branches. `PathRSpace.SubspaceSystem` records the no-implicit-
interaction discipline: a concrete model has to prove that every reaction comes from an explicit cut and
that the cut exposes comparable paths.

The cost-accounting papers add a second interface. `Costed.CostedLTS` is a labelled transition system
whose steps carry a cost. `Costed.CostedLTS.forget` drops the cost annotation and recovers the ordinary
behavioural system. The theorem `Costed.Trace.to_reflTransGen` proves that any finite costed trace is an
ordinary trace after costs are forgotten. That is the checked kernel of the story told by the cost
endofunctor and cost-accounted rho papers: phlogiston and token stacks refine behaviour, they do not
replace the behaviour relation {citep continuedGSLTCost}[] {citep costAccountedRho}[]. The spacetime
paper sits one layer beyond that, reading spent cost as the measure of a causal history
{citep costSpacetime}[].

The Lean files are interfaces and small kernels, not the knotted topos. The current release proves the
operational pieces that such a denotation must respect: `RewStep`, `RewStepMany`, executable soundness,
OSLF predicates, greatest-fixed-point OSLF safety, confluence fragments, AC rewriting, the Cordial
Miners runtime embedding, and the rho COMM/RSpace fragment in `MeTTaIL.Semantics.Rho`. The rho
desugaring functor, the location-channel operational correspondence, the final
behaviour coalgebra in a knotted topos, the path-key trie store, the cut distributive law, subspace
reaction confluence, the set-automaton channel compiler, the cost endofunctor itself, and the calibration
between context bisimulation and each object language's usual observational equivalence are still not
formalized. Those are the real next theorems if the claim that a spec gets a denotation automatically is
to become machine checked.

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

The book's MeTTa kernel and the MeTTaIL framework meet in a bridge: an embedding of the kernel's
`Metta.Atom` (the four metatypes) into GSLT terms. A symbol becomes a nullary constructor, a variable
a GSLT variable, an expression a wild-labelled application, and a grounded atom a keyed nullary
constructor. The embedding is injective on the grounded-free fragment; grounded atoms inherit the same
IEEE-754 float caveat the kernel documents for its own equality. The bridge is the precise sense in which
MeTTa is a GSLT object language.

The metatheory layer rounds this out: decidable equality and a lawful Boolean equality for the whole
data model, the pipeline invariants (each transformation touches only the term list), and the
presentation algebra's set laws (union, intersection, and difference behave as set operations on each
component).

# What Remains Open

The deepest layer is still a research target. MeTTaIL's modal type system, the possibility modalities,
and the recovery of arrow types in the design notes are sketched in the source, but the release does not
claim that typing theorem. The rho and knotted-topoi papers give the denotational route, and the new Lean
interface states the theorem to prove, but the knotted topos and the MeTTaIL-to-rho desugaring are not yet
formalized. We formalize the determinate fragments and mark the open parts in place. The Scala tool's own
`--hypercube` pass omits the modal types too, and our type-lift matches the tool, not the unfinished note.
The per-variable category-consistency check of the elaborator's type checker remains future work; the
category-match and bound-variable checks are in place.

Building a faithful model is also a good way to find bugs in the thing you are modeling, and we found a
few in the tool's rename and checking code. Where the Scala does something wrong, an export rename that
overwrites every rule's output sort, a static check that only inspects the first export, a checker that
does not descend through `let`, the Lean does the correct thing and leaves a note at the divergence.
The five we found are written up for the F1R3FLY team in `MeTTaIL/HYPERON_IMPROVEMENTS.md`.
