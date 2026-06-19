# Sources and alignment notes

## Uploaded paper

- Ben Goertzel, **Reflective Metagraph Rewriting as a Foundation for an AGI “Language of Thought” — Toward a Formalization of OpenCog Hyperon’s MeTTa Language in Terms of Algebraic Metagraph Rewriting**, arXiv:2112.08272v1. Used for MeTTa vocabulary, types, pattern matching, equality, interpretation, graph/metagraph rewriting, grounding domain, `@` activation, VBTO, transform, reflection, execution traces, Ruliad/topos direction, and efficient-pattern-matching discussion.
- Ben Goertzel, **Hyperon for AGI ⇒ ASI: Whitepaper 2025**. Used for the Graph-Structured Lambda Theory (GSLT) foundation (§3.4.1): the design goal of mechanically deriving an interpreter and a type system from one formal semantics and keeping them in correspondence. This is the design intent that the kernel-to-MOPS reduct-set correspondence (`MettaHyperonFull/Proofs/Correspondence.lean`) makes machine-checked at the QUERY step.

## Online sources checked

- trueagi-io/hyperon-experimental GitHub repository. Used for current implementation shape: Rust core, atomspace/interpreter implementation, Python/C APIs, REPL, Docker/PyPI paths, and docs pointers.
- hyperon.opencog.org. Used for the high-level design claim that MeTTa programs combine functional, logical, and process-calculus-like programming and operate by querying/rewriting Atomspaces.
- metta-lang.dev tutorials. Used for current surface concepts around equality/reduction, type assignment, spaces, matching, and atomspace operations.
- MeTTa Standard Library documentation. Used to ensure runtime/stdlib category coverage: equality, error handling, evaluation control, expression manipulation, math, nondeterminism, types, lists, atomspace interaction, quoting, and set operations.
- arXiv:2305.17218, **Meta-MeTTa: an operational semantics for MeTTa**. Used for the operational-semantics perspective.
- Adam Vandervorst’s Scala FormalMeTTa. Used as a secondary reference for the four-space state shape and rewrite-rule naming.
- Lean 4/Lake documentation. Used for the Lake project layout and Lean 4 module organisation.
