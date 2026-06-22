/- jscpd:ignore-start -/
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
/- jscpd:ignore-end -/

The appendix collects the reference material that used to live in separate files at the repository root.
The appendix states what is machine-checked, where each MeTTa and Hyperon topic is formalized, and how
the development compares with Hyperon's current implementation.

# Proof Status

The development separates three things that are easy to conflate:

 * results checked by Lean in the active build;
 * earlier exploration kept under `archive/` but not compiled;
 * work that is planned but not yet formalized.

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
   `Consistent.not_transitive` and `matchType_not_transitive` (`Proofs/Gradual.lean`).
 * *Alpha-equivalence* is an equivalence relation, preserves size, and coincides with `=` on closed
   atoms: `alphaEq_equivalence`, `AlphaEq.size_eq`, `alphaEq_iff_eq_of_closed` (`Proofs/Alpha.lean`).
 * *Substitution laws* used by binding propagation and preservation (`Proofs/Substitution.lean`).
 * *Operational semantics.* The four-register machine, append-only knowledge-base auditability, and
   gas non-creation (`Operational/Properties.lean`), with a bisimulation tying the indexed kernel to
   the published semantics at the level of rule firing: `kernel_mops_bisim`
   (`Proofs/Correspondence.lean`).

## Archived exploration, not part of the verified build

The following were modelled in an earlier, approximate form. They live under `archive/`, are not compiled
by the build, and must not be read as part of the verified development. See `archive/README.md`. They
are listed so the proof status is not mistaken for covering them.

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

The coverage map points each MeTTa and Hyperon topic to the files that formalize it. The runtime is a
formal reference: small enough to inspect and explicit about every host contract. The runtime is not a
drop-in replacement for the Rust Hyperon runtime and does not cover the full Hyperon feature surface.

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
`Space.transform` (query then instantiate) is a helper in `Core/Space.lean` that the operational
specification uses for its `transform` and `match` steps (`Operational/Semantics.lean`). The helper is
not an instruction of the executable interpreter, whose `match` is implemented by `matchConj`.

# Improvements over Hyperon

Hyperon's minimal MeTTa interpreter (`hyperon-experimental/lib/src/metta/interpreter.rs`) is, by its
authors' description, in an alpha state. Its source carries a self-described "hack" and several `TODO`
notes at the points that decide evaluation. The written semantics is prose and pseudocode without proofs.

LeaTTa is a companion to that work: a total, machine-checked semantics that agrees with Hyperon's own
test oracle (270 of 270), replaces mutable and ad-hoc machinery with declarative constructs, and proves
properties the implementation only asserts.

## What is proved

The metatheory proves what the implementation asserts in comments. The full list with theorem names is
under Proof Status above. In short, the proved surface covers determinism, confluence of the deterministic
fragment, sound and complete first-argument indexing, gradual-type permissiveness and faithful errors,
alpha-equivalence, and the kernel-to-specification bisimulation.

One foundational choice matters for the proofs. `Atom`'s `BEq` is hand-written and structural rather than
derived, so it is kernel-reducible and the indexing and type proofs go through. The derived instance
compiles to opaque well-founded recursion that blocks equational reasoning.

## Hyperon source markers and their treatment

The Hyperon sources carry explicit markers (`TODO`, hotfix, and "hack" comments) at points that decide
evaluation. Each is matched here by a declarative construct.

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

Hyperon's own unmodified tests run through this interpreter (`scripts/run-oracle.sh`) and pass 270 of 270
across 22 files, on the minimal interpreter rather than a curated subset. The passing set includes the
full dependent-type tier (`d1` through `d5`): GADTs, higher-order functions, dependent length arithmetic,
types as propositions, and auto type-checking with `BadArgType`, along with the documentation operators
`get-doc` and `help!`.

One file is left out: `f1_imports.metta`. Its authors mark it Python-mode-only, because it assumes
`&self` starts nearly empty with `corelib` and `stdlib` as separate importable modules, while this build
ships the prelude inside `&self`.

The module machinery it would exercise, `import!` into named spaces and diamond-dependency deduplication,
is covered by `c2_spaces` (25/25) and `g1_docs` (10/10). The corpus is vendored under `tests/corpus/`
(MIT, commit `3f76dc4`), so the oracle reproduces 270/270 from a clean clone and fails the build on any
divergence.

# Sources and Alignment

Here are the sources this development draws on.

## Papers

 * Ben Goertzel, *Reflective Metagraph Rewriting as a Foundation for an AGI Language of Thought*
   (arXiv:2112.08272): MeTTa's vocabulary, types, pattern matching, equality, grounding, transform,
   reflection, and execution traces.
 * Ben Goertzel, *Hyperon for AGI to ASI: Whitepaper 2025*, section 3.4.1: the Graph-Structured
   Lambda Theory (GSLT), deriving an interpreter and a type system from one formal semantics and
   keeping them in correspondence. That intent is what the kernel-to-MOPS reduct-set correspondence
   makes machine-checked at the QUERY step.
 * Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, and Adam Vandervorst, *Meta-MeTTa: an
   Operational Semantics for MeTTa* (arXiv:2305.17218): the four-register machine and bisimulation.
 * Mike Stay and Lucius Gregory Meredith, *Logic as a Distributive Law* (arXiv:1610.02247) and
   *Representing operational semantics with enriched Lawvere theories* (arXiv:1704.03080): OSLF,
   spatial/behavioral modalities, and the GSLT route from operational rules to logic.
 * Lucius Gregory Meredith, *A Knotted Universe*, *Quoting is Colour-Swap*, *Paths are Subspaces*,
   the cost-accounting manuscripts, and *Knotted Topoi*: the route from rho-calculus context
   bisimulation to fully abstract denotational semantics for finitely presentable GSLTs, plus the
   path-key and cost refinements that the runtime story has to respect.
 * Jon Beck, *Distributive laws* (1969), and Ross Street, *The formal theory of monads* (1972):
   the composite-monad theorem and the 2-categorical monad setting formalized in
   `MeTTaILProofs/DistributiveLaw.lean`.

## Paper-to-formalization map

The map below states what each source supports in the Lean development, and what it does not claim.

 * Goertzel's metagraph rewriting paper {citep goertzelMetagraph}[] supports the atom language,
   equality-rule reduction, matching, spaces, grounding, and traces. The Lean surface is
   `MettaHyperonFull/Core`, `MettaHyperonFull/Minimal`, and the oracle-backed executable. The checked
   claims include first-argument indexing soundness and completeness (`matchAtoms_headKey`,
   `candidates_sound`, `candidates_complete`) and QUERY soundness/completeness
   (`mem_equalityReductions`). The claim is not that every current Hyperon import/runtime feature is
   reimplemented; the exact corpus boundary is the 270/270 oracle run described above.
 * The MOPS paper {citep mops}[] supports the four-register machine, barbed bisimulation, and the
   QUERY/CHAIN/ADD/REM/OUTPUT step split. The Lean surface is `Operational/State.lean`,
   `Operational/Semantics.lean`, `Operational/Bisimulation.lean`, and `Operational/Properties.lean`.
   The checked claims include `kernel_mops_bisim`, `smallStep?_kb_auditable`,
   `resourceStep?_energy_nonincreasing`, and the command-consumption theorems
   `stepAddAtom_input_eq` / `stepRemAtom_input_eq`. The claim is not that the operational machine and
   the minimal interpreter are the same artifact; the theorem states their reduct-level correspondence.
 * The MeTTaIL runtime modules set the spec-to-runtime contract: derive a reducer from a presentation
   and prove each executable step sound against the induced relation. The Lean surface is
   `MeTTaIL/Semantics/Context.lean`,
   `Eval.lean`, `Normal.lean`, `Terminate.lean`, `Strategy.lean`, `WellSorted.lean`, and
   `Runtime/Generic.lean`. The checked claims include `oneStep_sound`, `eval_sound`,
   `eval_reaches_normal`, and `subjectReduction_base`. The claim is conditional where rewriting theory
   is conditional: unique normal forms require termination and confluence hypotheses.
 * The rewriting-theory route uses Newman's lemma and the Knuth-Bendix-Huet critical-pair criterion.
   The Lean surface is `MeTTaILProofs/Newman.lean`,
   `CriticalPairs.lean`, `ConditionalCP.lean`, and `ConditionalCPRuntime.lean`. The checked claims
   include `confluent_of_CPJ`, `c_confluent_of_joins`, `RuntimeCongruenceStep.reachable`, and
   `cong_RewStep_confluent_on_emb`. The runtime bridge covers runtime congruence schemas; genuinely
   non-congruence multi-step side conditions remain in the abstract conditional-rewriting layer.
 * Stay and Meredith's OSLF papers {citep stayMeredithLogic}[] {citep enrichedLawvereSemantics}[]
   support the spatial and behavioral modalities. The Lean surface is `MeTTaIL/Semantics/OSLF.lean`,
   `MeTTaILProofs/OSLFRec.lean`, and `MeTTaILProofs/OSLFCat.lean`. The checked claims include
   `arrow_eq_diaCtx`, `box_preserved`, and the greatest-fixed-point invariance lemmas. The claim is not
   that every construction in the papers has been mechanized; the mechanized part is the predicate-model
   core used by this runtime story.
 * The rset, rho, path-key RSpace, cost-accounting, and knotted-topoi manuscripts
   {citep knottedUniverse}[] {citep quotingColourSwap}[] {citep pathsSubspaces}[]
   {citep continuedGSLTCost}[] {citep costAccountedRho}[] {citep costSpacetime}[]
   {citep knottedTopoi}[] support the denotational target. The ITM, CZ2, and Jetta repositories
   {citep itmScalaState}[] {citep cz2Repository}[] {citep jettaRuntime}[] support the store-facing
   interface. Williams and Stay's Native Type Theory supplies the sort-predicate native-type target
   {citep nativeTypeTheory}[]. Goertzel's typed-metagraph Galois-connection paper supplies the
   search/objective reading of the generic bridge {citep patternsOfCognition}[]. Dedukti and Lambdapi
   are the closest proof-framework comparison points for native types plus rewriting
   {citep deduktiLogicalFramework}[] {citep lambdapiDocs}[]. The MeTTapedia native grammatical
   formalism paper supplies the surface-invariance pattern used for native readings
   {citep nativeGrammaticalFormalism}[]. Stay, Meredith, and Wells' generated-hypercubes draft supplies
   the finite slot-center reading of generated modal and spatial type systems
   {citep generatedHypercubes}[]. The Lean surface is
   `MeTTaIL/Semantics/Denotational.lean`, `MeTTaIL/Semantics/Native.lean`,
   `MeTTaIL/Semantics/NativeGrammar.lean`, `MeTTaIL/Semantics/NativeTypes.lean`,
   `MeTTaIL/Semantics/Hypercube.lean`, `MeTTaIL/Semantics/CostRoundTrip.lean`,
   `MeTTaIL/Semantics/KnottedUniverse.lean`,
   `MeTTaIL/Semantics/RSet.lean`, `MeTTaIL/Semantics/Rho.lean`,
   `MeTTaIL/Semantics/RhoKMachine.lean`, `MeTTaIL/Semantics/RhoCompiler.lean`, and
   `MeTTaIL/Semantics/InteractingTrieMap.lean`.
   The checked claims include
   `bisimilar_isBisimulation`, `fullyAbstract_of_kernel`, `FullyAbstractModel.eq_iff_bisimilar`,
   `fullyAbstract_of_calibration`, `fullyAbstract_of_observation_calibration`,
   `StepTranslation.bisimilarityPreserving`, `StepTranslation.bisimilarityReflecting`,
   `NativeCarrier.toFullyAbstractModel`, `NativeCarrier.eq_iff_bisimilar`,
   `NativeCarrier.typeOf_eq_of_step`, `NativeSurface.SameNative.type_eq`,
   `NativeSurface.SameNative.denote_eq`, `NativeSurface.SameNative.bisimilar`,
   `NativeEvidenceModel.evidence_eq_of_sameNative`,
   `NativeQueryModel.evidence_eq_of_sameNative`, `NativeGaloisBridge.diamond_le_iff`,
   `NativeGaloisBridge.searchSpec_iff_objectiveSpec`, `NativeGaloisBridge.le_box_diamond`,
   `NativeGaloisBridge.diamond_box_le`, `NativeGaloisBridge.diamond_mono`,
   `NativeGaloisBridge.box_mono`,
   `Pred.future_box_galois`, `Pred.dia_pastBox_galois`,
   `NativeType.constructor_satisfies_iff`, `NativeType.spatial_satisfies_sexp_iff`,
   `NativeType.arrow_satisfies_iff`, `NativeType.sortedBox_preserved`,
   `Hypercube.Equation.admissible_iff`, `Hypercube.centerMember_iff`,
   `Hypercube.mem_equationalCenter_iff`, `Hypercube.equationalCenter_sound`,
   `Hypercube.equationalCenter_complete`, `AST.hypercubeContextVarsAt?_root`,
   `AST.mem_hypercubeSubterms_root`, `Hypercube.SlotFamily.outputSlot_mem_slots`,
   `Hypercube.SlotFamily.head_sortOp_eq`, `Hypercube.ModalSite.slotFamily_slots_length`,
   `Hypercube.ModalSite.outputSlot_mem_slotFamily`,
   `Hypercube.SpatialHead.slotFamily_slots_length`,
   `Hypercube.SpatialHead.outputSlot_mem_slotFamily`,
   `Hypercube.TypeFamily.slotFamily_modal`, `Hypercube.TypeFamily.slotFamily_spatial`,
   `Hypercube.RuleScheme.outputSlot_mem_slotFamily`, `Hypercube.ModalSite.ruleKinds_length`,
   `Hypercube.ModalSite.ruleSchemes_length`, `Hypercube.SpatialHead.ruleKinds_length`,
   `Hypercube.SpatialHead.ruleSchemes_length`,
   `Bisimilar.trans`,
   `PathRSpace.comparable_iff_nonempty_subspaceBranch`, `Costed.costedStep_forget`,
   `Costed.Trace.to_reflTransGen`, `Costed.costDeadlocked_iff_forget_deadlocked`,
   `Costed.Trace.to_stepCount`, `Costed.Trace.to_stepCount_of_unitTokenCosted`,
   `Costed.ContinuedCostSystem.starved_deadlocked`,
   `Costed.ContinuedCostSystem.wrapped_trace_preserved`,
   `Costed.CostRoundTrip.image_iff_fixed`, `eval_rewrite_trace`, `Rho.listener_step`,
   `Rho.RSpace.comm_to_step_one`, `Rho.KMachine.creation_to_struct`, `Rho.KMachine.step_to_rho`,
   `Rho.KMachine.ordinaryReceive_to_rho`, `Rho.KMachine.persistentOutput_to_rho`,
   `Rho.KMachine.persistentReceive_to_rho`, `Rho.KMachine.persistentBoth_to_rho`,
   `Rho.Compiler.contractumRun_struct_kSource`, `Rho.Compiler.contractum_kstep_to_rho`,
   `Rho.Compiler.contractumRun_kstep_to_rho`,
   `Rho.Compiler.applyBaseRewrite_reduces_and_emits`, and
   `Rho.Compiler.applyBaseRewrite_reduces_emits_and_reifies_kstep`,
   `KnottedUniverse.Colour.swap_swap`,
   `KnottedUniverse.ReflectiveUniverse.dropRed_quoteRed`,
   `KnottedUniverse.ReflectiveUniverse.quoteRed_dropRed`,
   `KnottedUniverse.ReflectiveUniverse.dropBlack_quoteBlack`,
   `KnottedUniverse.ReflectiveUniverse.quoteBlack_dropBlack`,
   `KnottedUniverse.ReflectiveUniverseHom.id`,
   `KnottedUniverse.ReflectiveUniverseHom.comp`,
   `KnottedUniverse.ReflectiveUniverseHom.ext`,
   `KnottedUniverse.ReflectiveUniverse.category`,
   `KnottedUniverse.CoalgebraHom.id`,
   `KnottedUniverse.CoalgebraHom.comp`,
   `KnottedUniverse.CoalgebraHom.ext`,
   `KnottedUniverse.Coalgebra.category`,
   `KnottedUniverse.FinalCoalgebra.lift_commutes`,
   `KnottedUniverse.FinalCoalgebra.finalHom`,
   `KnottedUniverse.FinalCoalgebra.finalHom_unique`,
   `KnottedUniverse.FinalCoalgebra.isTerminal`,
   `KnottedUniverse.FinalCoalgebra.identity`,
   `KnottedUniverse.FinalBehaviourModel.toFullyAbstractModel`,
   `KnottedUniverse.FinalBehaviourModel.eq_iff_bisimilar`,
   `KnottedUniverse.FinalBehaviourModel.fullyAbstractFor`,
   `KnottedUniverse.FinalBehaviourModel.fullyAbstractForObservations`,
   `RSetModel.twoColourAutomaton_no_self_loop`,
   `RSetModel.RElem.quoteAtom_dropAtom`,
   `RSetModel.RSet.renameAtoms_eq_of_forall_mem_atomsOf`,
   `RSetModel.RSet.renameAtoms_eq_of_supports`,
   `RSetModel.RSet.renameAtoms_id`,
   `RSetModel.RSet.toExt_eq_of_extEq`,
   `RSetModel.RSet.mem_union_iff`,
   `RSetModel.RSet.extEq_union_congr`,
   `RSetModel.RSet.extEq_empty_union`,
   `RSetModel.RSet.extEq_union_empty`,
   `RSetModel.RSet.extEq_union_idem`,
   `RSetModel.RSet.extEq_union_comm`,
   `RSetModel.RSet.extEq_union_assoc`,
   `RSetModel.blackToRedSet_redToBlackSet`,
   `RSetModel.redToBlackSet_blackToRedSet`,
   `RSetModel.reflective_dropRed_quoteRed`,
   `RSetModel.reflective_quoteRed_dropRed`,
   `RSetModel.reflective_dropBlack_quoteBlack`,
   `RSetModel.reflective_quoteBlack_dropBlack`,
   `RSetModel.reflective_redBlackSetSwap`,
   `RSetModel.reflective_blackRedSetSwap`,
   `RSetModel.reflective_redBlackAtomSwap`,
   `RSetModel.reflective_blackRedAtomSwap`,
   `InteractingTrieMap.RITM.ofStep_toStep`, `InteractingTrieMap.RITM.toStep_ofStep`,
   `InteractingTrieMap.RITM.stepEquiv`,
   `InteractingTrieMap.PackedBinding.root_prefix_address`,
   `InteractingTrieMap.PackedBinding.root_comparable_address`, and
   `InteractingTrieMap.Colour.swap_swap`. The claim is not that the knotted topos, full rho
   desugaring, trie store, cut distributive law, cost endofunctor, causal-set functor, or final
   coalgebra has been constructed in Lean. The checked modules state the proof interfaces, COMM
   kernels, the K one-pair creation and ready-pair guarded ordinary and persistent input/output cell
   steps, the packet-level base-rewrite bridge, the red/black quote/drop and final-coalgebra
   interfaces, the finitary rset atom-supply, finite-support, exact-member quotient, and finite-union
   core, the ITM roll/unroll surface, and the packed-binding prefix connector that those constructions
   must instantiate.
 * The MeTTa-calculus, Turing-to-rho, and optimal-channel papers {citep mettaCalculus}[]
   {citep rhoViaTuring}[] {citep optimalChannels}[] support the compiler direction from MeTTaIL/GSLT
   presentations to rho/RSpace. The current release uses them as a roadmap, not as completed
   mechanization: the set-automaton channel compiler, outermost-preserving channel quotient, and
   Turing-machine encoding are not yet Lean developments.
 * The boundaried-monoid and reputation papers {citep boundariedMonoids}[] {citep reputationFramework}[]
   are adjacent to the current formalization. Boundaried monoids line up with partial composition by
   matching boundaries, and the reputation paper lines up with evidence-indexed OSLF modalities and the
   PoR-weighted Cordial Miners motivation. They are not counted as checked claims in this release.
 * Beck and Street {citep beckDistributiveLaws}[] {citep streetFormalTheoryMonads}[] support the
   categorical backbone. The Lean surface is `MeTTaILProofs/DistributiveLaw.lean`; the checked headline
   is `MeTTaIL.Beck.DistributiveLaw.composeMonad`. The claim is not a full formalization of Street's
   paper, only the composite-monad theorem needed here.

## Other sources checked

 * The `trueagi-io/hyperon-experimental` repository, for the current implementation shape.
 * The local `/home/user/Dev/mettatron-workspace` checkout, especially
   `MeTTa-Compiler/src/pathmap_par_integration.rs` and
   `f1r3node/rholang/src/rust/interpreter/reduce.rs`, for the concrete `Par` and RSpace boundary.
 * `hyperon.opencog.org` and the `metta-lang.dev` tutorials, for surface concepts: equality and
   reduction, type assignment, spaces, matching, and atomspace operations.
 * The MeTTa standard library documentation, for runtime and stdlib coverage.
 * Adam Vandervorst's Scala FormalMeTTa, for the four-space state shape and rewrite-rule naming.
 * The Lean 4 and Lake documentation, for the project layout.
