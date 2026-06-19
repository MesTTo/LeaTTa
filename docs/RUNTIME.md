# Runtime notes

The Lean runtime is intentionally small but covers the semantics spine:

- parses S-expression-like MeTTa atoms;
- stores ordinary atoms as knowledge-base atoms;
- treats `!` forms as input/evaluation requests;
- loads equality rules `(= L R)` into the space;
- performs directional equality reduction by matching `L` against a query and instantiating `R`;
- implements `match`, `transform`, `add-atom`, `remove-atom`, `get-atoms`, selected atom operations, selected math operations, nondeterministic outputs, and quoted/unquoted forms;
- returns result lists to model MeTTa nondeterminism.

The runtime is not a drop-in replacement for the active Rust Hyperon runtime. It is a formal reference runtime: small enough to inspect, broad enough to test the formal semantics, and explicit about all host/runtime contracts.
