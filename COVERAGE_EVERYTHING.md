# Coverage: MeTTa and Hyperon topics, and where they are formalized

This document maps the MeTTa and Hyperon topics drawn from the source papers, the Meta-MeTTa
operational semantics, the current Hyperon implementation, and the public standard-library
documentation, to the files that formalize them. It is organized in two parts: the
machine-checked core that is built, and the earlier exploratory models that now live under
`archive/` and are not built. See `archive/README.md`.

## Faithful core (built and validated)

### Object language and matching

| Topic | Where |
|---|---|
| MeTTa as a meta-language with a single atom type | `Core/Atom.lean` |
| Symbols: grounded values, constant symbols, variables | `Core/Atom.lean` |
| Expressions as recursively nested trees | `Core/Atom.lean` |
| Grounding domain and grounded operations | `Core/Grounding.lean`, `Core/Builtins.lean` |
| Pattern matching and unification | `Core/Matching.lean`, `Core/Unification.lean` |
| Variable binding and substitution (VBTO) | `Core/Substitution.lean`, `Core/Bindings.lean` |
| α-equivalence of atoms | `Core/Alpha.lean`, `Proofs/Alpha.lean` |
| Atomspaces as spaces of expressions | `Core/Space.lean` |

### Evaluation and the standard library

| Topic | Where |
|---|---|
| The minimal instruction set (`eval`, `chain`, `unify`, `cons-atom`, `function`/`return`, and so on) | `Minimal/Interpreter.lean` |
| Equality `(= L R)` as directed reduction | `Minimal/Interpreter.lean` (`queryOp`), `Operational/Semantics.lean` |
| Evaluation as an equality query | `Minimal/Interpreter.lean`, `Operational/Semantics.lean` |
| First-argument rule indexing | `Minimal/Interpreter.lean` (`MinEnv.candidates`), `Proofs/IndexingComplete.lean` |
| Nondeterminism (`superpose`, `collapse`), reified as a result list | `Minimal/Interpreter.lean` |
| Control and list operations (`if`, `let`, `case`, `switch`, `map-atom`, `filter-atom`, `foldl-atom`) | `Minimal/Stdlib.lean` |
| Set operations (`unique`, `union`, `intersection`, `subtraction`) | `Minimal/Stdlib.lean` |
| Expression manipulation (`cons-atom`, `decons-atom`, `car`, `cdr`, `size`, `index`) | `Core/Builtins.lean`, `Minimal/Stdlib.lean` |
| Arithmetic, mixed integer and float | `Core/Builtins.lean` |
| Error handling (`Error`, `BadArgType`, the `assert*` family) | `Core/Result.lean`, `Minimal/Stdlib.lean` |
| Add and remove atoms, self-modification of the knowledge base | `Minimal/Interpreter.lean` (`add-atom`, `remove-atom`) |
| Mutable spaces and state cells, `import!` | `Core/Space.lean`, `Minimal/Stdlib.lean` |

### Types

| Topic | Where |
|---|---|
| Type assignment `(: a T)` and the `Type` symbol | `Core/Types.lean`, `Minimal/Interpreter.lean` (`getTypes`) |
| Arrow types `(-> B A)` and function-application checking | `Core/Types.lean`, `Minimal/Interpreter.lean` (`typeCheckArgs`) |
| Gradual typing: `%Undefined%` and `Atom`, consistency `~` | `Minimal/Interpreter.lean` (`matchType`), `Proofs/Gradual.lean` |
| Typed pattern matching and variable priority | `Core/Matching.lean`, `Core/Types.lean` |

### Operational semantics and metatheory

| Topic | Where |
|---|---|
| The published Meta-MeTTa four-register machine (arXiv 2305.17218) | `Operational/Semantics.lean` |
| Barbed bisimulation and program equivalence | `Operational/Bisimulation.lean` |
| Resource-bounded (gas) evaluation | `Operational/ResourceBounded.lean` |
| Execution traces | `Operational/Trace.lean` |
| Determinism and confluence of the deterministic fragment | `Proofs/Results.lean`, `Proofs/Confluence.lean` |
| Indexing soundness and completeness | `Proofs/Indexing.lean`, `Proofs/IndexingComplete.lean` |
| Type soundness: permissiveness, faithful errors, preservation | `Proofs/TypeSoundness.lean`, `Proofs/Preservation.lean` |
| Kernel-to-specification correspondence at the QUERY step | `Proofs/Correspondence.lean` |

## Archived exploration (kept for reference, not built)

The following topics were modelled in earlier, approximate form and are retained under `archive/`.
They are not part of the faithful core and are not compiled.

| Topic | Where (under `archive/`) |
|---|---|
| Single-pushout (SPO) and double-pushout (DPO) graph rewriting | `Metagraph/SPO.lean`, `Metagraph/DPO.lean` |
| Directed labelled metagraph homomorphism | `Metagraph/Homomorphism.lean` |
| Expression-to-DAG and sub-metagraph encoding | `Metagraph/Encoding.lean`, `Metagraph/Basic.lean` |
| Enrichments such as embedding vectors | `Metagraph/Basic.lean`, `Interop/Host.lean` |
| Quotation and self-modification at the object level | `Reflection/Quotation.lean`, `Reflection/SelfModification.lean` |
| Execution-trace history and the Ruliad perspective | `Reflection/History.lean`, `Reflection/Ruliad.lean` |
| Host and distributed-atomspace (DAS) contracts | `Interop/Host.lean`, `Interop/DAS.lean` |
| Well-formedness metatheory over the earlier runtime | `MetaTheory/WellFormed.lean` |
| The earlier four-register runtime and CLI | `Runtime/Evaluator.lean`, `Runtime/Program.lean`, `Runtime/CLI.lean` |
