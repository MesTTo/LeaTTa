/-
LeaTTa: bibliography.
Citable references for the LeaTTa manual (the analogue of a `.bib` file), defined as Verso
reference values. Cite with {citet x}[], {citep x}[], or {citehere x}[].
-/
import VersoManual
open Verso.Genre.Manual

namespace Docs

/-- Meredith, Goertzel, Warrell & Vandervorst; the published operational semantics of MeTTa (MOPS). -/
def mops : ArXiv where
  title := inlines!"Meta-MeTTa: an Operational Semantics for MeTTa"
  authors := #[inlines!"Lucius Gregory Meredith", inlines!"Ben Goertzel",
               inlines!"Jonathan Warrell", inlines!"Adam Vandervorst"]
  year := 2023
  id := "2305.17218"

/-- Goertzel; metagraph-rewriting foundation for MeTTa ("Meta Type Talk"). -/
def goertzelMetagraph : ArXiv where
  title := inlines!"Reflective Metagraph Rewriting as a Foundation for an AGI Language of Thought"
  authors := #[inlines!"Ben Goertzel"]
  year := 2021
  id := "2112.08272"

/-- Stay & Meredith; OSLF and the distributive-law view of operational semantics. -/
def stayMeredithLogic : ArXiv where
  title := inlines!"Logic as a Distributive Law"
  authors := #[inlines!"Mike Stay", inlines!"Lucius Gregory Meredith"]
  year := 2016
  id := "1610.02247"

/-- Stay & Meredith; enriched Lawvere theories as a source of operational semantics. -/
def enrichedLawvereSemantics : ArXiv where
  title := inlines!"Representing operational semantics with enriched Lawvere theories"
  authors := #[inlines!"Mike Stay", inlines!"Lucius Gregory Meredith"]
  year := 2017
  id := "1704.03080"

/-- Assaf et al.; Dedukti as a logical framework with user-defined rewrite rules. -/
def deduktiLogicalFramework : ArXiv where
  title := inlines!"Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory"
  authors := #[inlines!"Ali Assaf", inlines!"Guillaume Burel", inlines!"Raphaël Cauderlier",
               inlines!"David Delahaye", inlines!"Gilles Dowek", inlines!"Catherine Dubois",
               inlines!"Frédéric Gilbert", inlines!"Pierre Halmagrand", inlines!"Olivier Hermant",
               inlines!"Ronan Saillard"]
  year := 2023
  id := "2311.07185"

/-- Deducteam; Lambdapi user documentation on dependent types with rewriting rules. -/
def lambdapiDocs : Article where
  title := inlines!"What is Lambdapi?"
  authors := #[inlines!"Deducteam"]
  journal := inlines!"Documentation"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://lambdapi.readthedocs.io/en/latest/about.html"

/-- Oruzi; GF and OSLF bridge used as the native surface-invariance pattern. -/
def nativeGrammaticalFormalism : Article where
  title := inlines!"Native Grammatical Formalism: Verified Multilingual Semantics via GF and OSLF in Lean 4"
  authors := #[inlines!"Zar Oruzi"]
  journal := inlines!"Draft manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/zariuq/MeTTapedia/blob/main/papers/native-grammatical-formalism.pdf"

/-- Meredith; the red/black reflective set-theory construction used by the rho and topos papers. -/
def knottedUniverse : Article where
  title := inlines!"A Knotted Universe: a new notion of reflective set theories"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/tree/main/rset"

/-- Meredith; rho-calculus denotation in the knotted universe. -/
def quotingColourSwap : Article where
  title := inlines!"Quoting is Colour-Swap: a model of the rho calculus in the knotted universe"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/denotational-semantics-for-rho/knot-rho.pdf"

/-- Meredith; the path-key refinement of the RSpace store and its cut-triggered subspace dynamics. -/
def pathsSubspaces : Article where
  title := inlines!"Paths are Subspaces: a cut-triggered polymorphism of RSpace over path-keys, and its distributive law"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/polymorphic-rspace/paths-subspaces.pdf"

/-- Meredith; Turing-machine encoding into rho and the complexity reading of rho reductions. -/
def rhoViaTuring : Article where
  title := inlines!"From Turing's Machine to the Rho Calculus: An Introduction by Translation"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/FromTuringToRHO/rho_via_turing.pdf"

/-- Meredith; channel naming for compiling GSLT rewrite contexts into rho. -/
def optimalChannels : Article where
  title := inlines!"Optimal Channel Naming for Compositional Rewrite Translations via Set Automaton Partial Evaluation"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/optimal-channels/optimal-channels.pdf"

/-- Meredith; the cost endofunctor on continued interactive GSLTs. -/
def continuedGSLTCost : Article where
  title := inlines!"Continued Interactive GSLTs and the Cost Endofunctor"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/cost-accounting-as-monad/continued-gslt-cost-v2.pdf"

/-- Meredith; the rho instance of the cost-accounting construction. -/
def costAccountedRho : Article where
  title := inlines!"Cost-Accounted Rho Calculus: A Spectral Decomposition of Phlogiston"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/cost-accounting/cost-accounted-rho.pdf"

/-- Meredith; the causal-set reading of cost-accounted GSLT histories. -/
def costSpacetime : Article where
  title := inlines!"Spacetime from Cost: A functor from cost-accounted ciGSLTs to measured causal sets"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/cost-spacetime/spacetime-functor.pdf"

/-- Meredith; partial composition as boundary-aware algebra. -/
def boundariedMonoids : Article where
  title := inlines!"Boundaried Monoids via Comprehension: A purely equational theory"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/category-theory-via-monads/boundaried-monoids.pdf"

/-- Meredith; the categorical lift from the rho model to finitely presentable GSLTs. -/
def knottedTopoi : Article where
  title := inlines!"Knotted Topoi: the lift of the knotted set-theoretic universe, and fully abstract denotational semantics for the category of graph-structured lambda theories"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/knotted-topoi/knotted-topoi.pdf"

/-- Meredith; the MeTTa-calculus note and its RSpace compilation story. -/
def mettaCalculus : Article where
  title := inlines!"The MeTTa calculus"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2024
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/metta-calculus/metta-calculus.pdf"

/-- F1R3FLY-io; Scala sketch of the interacting-trie-map state equation. -/
def itmScalaState : Article where
  title := inlines!"Interacting trie maps: state equation sketch"
  authors := #[inlines!"F1R3FLY-io"]
  journal := inlines!"Source repository"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/itm/blob/main/src/main/scala/syntax/state.scala"

/-- Vandervorst; prefix-compressed expression storage and pattern lookup. -/
def cz2Repository : Article where
  title := inlines!"CZ2 prefix-compressed expression store"
  authors := #[inlines!"Adam Vandervorst"]
  journal := inlines!"Source repository"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/Adam-Vandervorst/CZ2"

/-- trueagi-io; Kotlin runtime with packed binding addresses for matched expressions. -/
def jettaRuntime : Article where
  title := inlines!"Jetta runtime space and packed binding store"
  authors := #[inlines!"trueagi-io"]
  journal := inlines!"Source repository"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/trueagi-io/jetta"

/-- Meredith; identity-indexed judgments and evidence-indexed OSLF modalities for reputation. -/
def reputationFramework : Article where
  title := inlines!"Identity-Indexed Typing Judgments and the Adjudication of Capability"
  authors := #[inlines!"Lucius Gregory Meredith"]
  journal := inlines!"Manuscript"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  pages := none
  url := "https://github.com/F1R3FLY-io/publications/blob/main/Reputation/reputation.pdf"

/-- Beck; the classical composite-monad theorem for distributive laws. -/
def beckDistributiveLaws : InProceedings where
  title := inlines!"Distributive laws"
  authors := #[inlines!"Jon Beck"]
  year := 1969
  booktitle := inlines!"Seminar on Triples and Categorical Homology Theory, Lecture Notes in Mathematics 80"
  url := "https://doi.org/10.1007/BFb0083084"

/-- Street; the 2-categorical formal theory of monads. -/
def streetFormalTheoryMonads : Article where
  title := inlines!"The formal theory of monads"
  authors := #[inlines!"Ross Street"]
  journal := inlines!"Journal of Pure and Applied Algebra"
  year := 1972
  month := none
  volume := inlines!"2"
  number := inlines!"2"
  pages := some (149, 168)
  url := "https://doi.org/10.1016/0022-4049(72)90019-9"

/-- Keidar, Naor, Poupko & Shapiro; the Cordial Miners leaderless DAG consensus protocol. -/
def cordialMiners : ArXiv where
  title := inlines!"Cordial Miners: Fast and Efficient Consensus for Every Eventuality"
  authors := #[inlines!"Idit Keidar", inlines!"Oded Naor", inlines!"Ouri Poupko",
               inlines!"Ehud Shapiro"]
  year := 2022
  id := "2205.09174"

/-- Meseguer; rewriting logic as a model of concurrency. -/
def meseguerRewritingLogic : Article where
  title := inlines!"Conditional Rewriting Logic as a Unified Model of Concurrency"
  authors := #[inlines!"José Meseguer"]
  journal := inlines!"Theoretical Computer Science"
  year := 1992
  month := none
  volume := inlines!"96"
  number := inlines!"1"
  pages := some (73, 155)
  url := "https://doi.org/10.1016/0304-3975(92)90182-F"

/-- Clavel et al.; the Maude rewriting-logic system and rewriting modulo equations. -/
def maudeBook : InProceedings where
  title := inlines!"All About Maude: A High-Performance Logical Framework"
  authors := #[inlines!"Manuel Clavel", inlines!"Francisco Durán", inlines!"Steven Eker",
               inlines!"Patrick Lincoln", inlines!"Narciso Martí-Oliet", inlines!"José Meseguer",
               inlines!"Carolyn Talcott"]
  year := 2007
  booktitle := inlines!"Lecture Notes in Computer Science 4350"
  url := "https://doi.org/10.1007/978-3-540-71999-1"

/-- Eker; even a restricted elementary AC matching problem is NP-complete. -/
def ekerSingleACMatching : Article where
  title := inlines!"Single Elementary Associative-Commutative Matching"
  authors := #[inlines!"Steven Eker"]
  journal := inlines!"Journal of Automated Reasoning"
  year := 2002
  month := some (inlines!"January")
  volume := inlines!"28"
  number := inlines!""
  pages := some (35, 51)
  url := "https://doi.org/10.1023/A:1020122610698"

/-- Dundua, Kutsia, and Marin; variadic AC matching with sequence variables. -/
def variadicACMatching : Article where
  title := inlines!"Variadic equational matching in associative and commutative theories"
  authors := #[inlines!"Besik Dundua", inlines!"Temur Kutsia", inlines!"Mircea Marin"]
  journal := inlines!"Journal of Symbolic Computation"
  year := 2021
  month := none
  volume := inlines!"106"
  number := inlines!""
  pages := some (78, 109)
  url := "https://doi.org/10.1016/j.jsc.2021.01.001"

/-- Berry and Boudol; the chemical abstract machine and multiset-style computation. -/
def chemicalAbstractMachine : Article where
  title := inlines!"The Chemical Abstract Machine"
  authors := #[inlines!"Gérard Berry", inlines!"Gérard Boudol"]
  journal := inlines!"Theoretical Computer Science"
  year := 1992
  month := none
  volume := inlines!"96"
  number := inlines!"1"
  pages := some (217, 248)
  url := "https://doi.org/10.1016/0304-3975(92)90185-I"

/-- Lamport; TLA and stuttering-insensitive behavior of action systems. -/
def lamportTLA : Article where
  title := inlines!"The Temporal Logic of Actions"
  authors := #[inlines!"Leslie Lamport"]
  journal := inlines!"ACM Transactions on Programming Languages and Systems"
  year := 1994
  month := none
  volume := inlines!"16"
  number := inlines!"3"
  pages := some (872, 923)
  url := "https://doi.org/10.1145/177492.177726"

/-- Siek & Taha; gradual typing; the source of the consistency relation `~`. -/
def siekTaha : InProceedings where
  title := inlines!"Gradual Typing for Functional Languages"
  authors := #[inlines!"Jeremy G. Siek", inlines!"Walid Taha"]
  year := 2006
  booktitle := inlines!"Scheme and Functional Programming Workshop"
  url := "http://scheme2006.cs.uchicago.edu/13-siek.pdf"

/-- de Moura & Ullrich; the Lean 4 theorem prover and programming language. -/
def lean4 : InProceedings where
  title := inlines!"The Lean 4 Theorem Prover and Programming Language"
  authors := #[inlines!"Leonardo de Moura", inlines!"Sebastian Ullrich"]
  year := 2021
  booktitle := inlines!"Automated Deduction - CADE 28"
  url := "https://doi.org/10.1007/978-3-030-79876-5_37"

/-- The Lean mathematical library (Mathlib). -/
def mathlib : InProceedings where
  title := inlines!"The Lean Mathematical Library"
  authors := #[inlines!"The mathlib Community"]
  year := 2020
  booktitle := inlines!"Certified Programs and Proofs (CPP 2020)"
  url := "https://doi.org/10.1145/3372885.3373824"

end Docs
