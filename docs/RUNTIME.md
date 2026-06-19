# Runtime notes

The Lean runtime covers the semantics spine:

- parses S-expression-like MeTTa atoms;
- stores ordinary atoms as knowledge-base atoms;
- treats `!` forms as input/evaluation requests;
- loads equality rules `(= L R)` into the space;
- performs directional equality reduction by matching `L` against a query and instantiating `R`;
- implements `match`, `transform`, `add-atom`, `remove-atom`, `get-atoms`, selected atom operations, selected math operations, nondeterministic outputs, and quoted/unquoted forms;
- returns result lists to model MeTTa nondeterminism.

Limitation: this is not a drop-in replacement for the Rust Hyperon runtime. It is a formal reference
runtime: small enough to inspect and explicit about all host/runtime contracts, but it does not
cover the full Hyperon feature surface.
