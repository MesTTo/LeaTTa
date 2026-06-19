# Appendix: Scope and Provenance

This appendix documents why each area of the MeTTa language covered by this
formalization is a high-value target for machine-checked treatment. The
justification is grounded in Hyperon's own source commentary: the development
comments in `hyperon-experimental` (Rust and MeTTa source at
`/home/user/Dev/hyperon-build-src`) identify areas where the semantics is still
settling, where a design decision has been deferred, or where the current
implementation is acknowledged to differ from the intended behavior. A
machine-checked reference is most useful precisely in those areas.

All paths below are absolute paths into the `hyperon-experimental` source tree.
Quoted text is verbatim from those sources. No markers have been added or
altered; all are present in the referenced files.

> Note on the local clone: it carries local modifications (see `UPSTREAM-PRS.md`)
> adding step-through-debugging instrumentation. The `panic!("test exceeded 50000
> steps — likely divergent")` at `interpreter.rs:2404` is a local test-harness
> edit, not an upstream developer-intent marker, and is excluded from the
> analysis below.

---

## 1. Type System (`lib/src/metta/types.rs`, `stdlib.metta`, `hyperon-atom`)

### Type-variable inference and propagation

`lib/src/metta/types.rs:379-385`:

```
// TODO: type of the variable could be actually a type variable,
// in this case inside each variant of type for the atom we should
// also keep bindings for the type variables. For example,
// we have an expression `(let $n (foo) (+ $n $n))`, where
// `(: let (-> $t $t $r $r))`, `(: foo (-> $tt))`,
// and `(: + (-> Num Num Num))`then type checker can find that
// `{ $r = $t = $tt = Num }`.
```

Variables are currently assigned no type (`vec![]`). The intended behavior is
full type-variable inference: bindings for type variables should be propagated
across an expression. The `get_atom_types_internal` function returns an empty
type list for `Atom::Variable(_)` as a consequence.

The Lean formalization's gradual type checker handles type-variable unification
for parametric and dependent signatures (`(-> $t $t ...)`, `(List $a)`) and is
proved faithful: `BadArgType` is reported exactly when and only when the checker
flags a mismatch (`mettaEval_badArgType`, `TypeSoundness.lean`).

### Unit type for the empty expression

`lib/src/metta/types.rs:397-399`:

```
// TODO: empty expression should have unit type (->), but type checking
// code cannot handle functional type which doesn't return value
Atom::Expression(expr) if expr.children().len() == 0 => vec![],
```

The empty expression `()` should carry type `(->)`, but the checker cannot
represent a function type with no return value. The empty expression currently
receives no type.

### Overloaded return convention for `get_atom_types`

`lib/src/metta/types.rs:494-512`:

```
// TODO: Three cases here:
// 1. function call types are not found
// 2. function call type with correct arg types are found
// 3. only function call type with incorrect arg types are found
//
// In (1) we should return `vec![ Undefined ]` from `get_atom_types()` when no types found;
// In (2) we should return the type which function returns but types are never empty;
// In (3) we should return empty `Vec` when types are empty, because `validate_atom()` expects
// empty `Vec` when atom is incorrectly typed.
...
// This is a tricky logic. To simplify it we could separate tuple and
// function application using separate Atom types. Or use an embedded atom
// to designate function application.
```

The three cases (type not found, correctly typed, ill-typed) are currently
encoded in a single `Option<Vec<...>>`/empty-`Vec` convention, which the
comment describes as tricky. The desired redesign separates tuple from
function-application at the `Atom` level. The Lean formalization makes this
distinction explicit through `argMask`/`returnsAtom` dispatch, decided once
from the operator's signature rather than re-derived during evaluation.

### Subtyping is under-constrained

`lib/src/metta/types.rs:42`:

```
// TODO: query should check that sub type is a type and not another typed symbol
```

`query_super_types` (which implements subtyping via `:<` / `isa_query`) does
not verify that the queried entity is actually a type; it can match ordinary
typed symbols. The subtyping relation is currently under-constrained.

### Performance note on tuple-type enumeration

`lib/src/metta/types.rs:488`: `// FIXME: ineffective` (in `get_tuple_types`).
This is a performance observation with no semantic consequence, noted here for
completeness.

### Test coverage gap

`lib/src/metta/types.rs:579`: `// TODO: write a unit test` (inside
`get_matched_types`, on the `make_variables_unique` + `match_reducted_types`
path). The matching-of-types code used in type-checking has a noted coverage
gap.

### Known divergences between current and intended type-checking behavior

Three test-module comments in `types.rs` document cases where the current
implementation accepts atoms that the developers consider ill-typed:

`lib/src/metta/types.rs:1177-1179`:

```
// TODO: (aF b) is incorrectly typed, but it is an Atom and check_type
// returns True
assert!(check_type(&space, &atom("(aF b)"), &ATOM_TYPE_ATOM));
```

`lib/src/metta/types.rs:1225-1227`:

```
// TODO: it is incorrectly typed, but (atomR a) is an Expression and
// check_type returns True
assert!(check_type(&space, &atom("(exprF (atomR a))"), type_r));
```

`lib/src/metta/types.rs:1298-1300`:

```
// TODO: (exprF (atomR a)) is incorrectly typed, but (atomR a)
// is an Expression and validate_atom returns True
assert!(validate_atom(&space, &atom("(exprF (atomR a))")));
```

When a meta-type (`Atom` or `Expression`) is the expected argument or return
type, `check_type`/`validate_atom` accept atoms that are ill-typed at the
ordinary-type level. The root is `check_meta_type` (`types.rs:615-616`):
`*typ == ATOM_TYPE_ATOM || *typ == get_meta_type(atom)` short-circuits the
deeper type check. The tests pin the current (accepting) behavior; the comments
note the intended (rejecting) behavior.

### The `->` type constructor has no type of its own

`lib/src/metta/runner/stdlib/stdlib.metta:367-370`:

```
; TODO: Type is used here, but there is no definition for the -> type
; constructor for instance, thus in practice it matches because -> has
; %Undefined% type. We need to assign proper type to -> and other type
; constructors but it is not possible until we support vararg types.
```

The `->` function-type constructor carries no type declaration; it passes
type-checking only because it falls through to `%Undefined%`. The developers
want proper types for `->` and other type constructors, but that requires
variadic type support, which is not yet implemented. This is a central
soundness gap in the gradual type system.

`lib/src/metta/runner/stdlib/stdlib.metta:617-618`:

```
; TODO: there is no way to define operation which consumes any number of
; arguments and returns unit
```

The same variadic limitation motivates the hand-written arities for `nop`.

### Grounded-atom typing is single-valued

`hyperon-atom/src/lib.rs:419-421`:

```
// TODO: type_() should return Vec<Atom> because of type non-determinism
// TODO: type_() could return Vec<&Atom> as anyway each atom should be replaced
// by its alpha equivalent with unique variables
```

A grounded atom may have multiple types (type non-determinism), but
`Grounded::type_()` returns a single `Atom`. The consequence is visible in
`types.rs:387-393`, where a grounded atom yields at most one `AtomType`.

`hyperon-atom/src/gnd/mod.rs:89-93`:

```
// TODO: this function is a hack which is introduced for embedded grounded
// types only. It should be replaced by some mechanism which allows defining
// a single grounded atom equality procedure in a MeTTa module. This could
// be done via defining a type class or equality function overloading.
```

Grounded-atom equality (`gnd_eq`) is acknowledged as a built-in-only
workaround; the intended design is a type-class or overloaded equality
definable in MeTTa itself.

---

## 2. Matching and Unification (`hyperon-atom/src/matcher.rs`)

### Asymmetric handling of Variable matched against GroundedAtom

`hyperon-atom/src/matcher.rs:1105-1108`:

```
// TODO: If GroundedAtom is matched with VariableAtom there are
// two way to calculate match: (1) pass variable to the
// GroundedAtom::match(); (2) assign GroundedAtom to the Variable.
// Returning both results breaks tests right now.
```

`match_atoms_recursively` currently takes only one branch (assign the grounded
atom to the variable) for the `Variable ~ Grounded` case; the alternative
(invoke the grounded atom's custom `match_`) is not combined because combining
both results breaks existing tests. A formalization must encode this deliberate
single-branch choice rather than the full binary relation.

### Termination under infinite result streams

`hyperon-atom/src/matcher.rs:1042-1044`:

```
//TODO: A situation where a MatchResultIter returns an unbounded (infinite) number of results
// will hang this implementation, on account of `.collect()`
```

Matching is not uniformly lazy: an infinite result stream hangs because results
are collected eagerly. This is relevant to any termination argument about the
matching procedure.

### Naming of key `BindingsSet` concepts

`hyperon-atom/src/matcher.rs:134`:
`// TODO: rename Bindings to Substitution which is more common term`

The `Bindings` type is a substitution in the standard formal sense.

`hyperon-atom/src/matcher.rs:981-983` (issue #281):

```
/// TODO: Need a better name that doesn't conflict with the intuitions about Bindings::is_empty()
```

on `BindingsSet::is_empty` (meaning: contains no Bindings, i.e., no match).

`hyperon-atom/src/matcher.rs:989-990` (issue #281):

```
/// TODO: Need a better word to describe this concept than "single"
```

on `BindingsSet::is_single` (meaning: one empty Bindings, i.e., unconstrained
match, always succeeds).

The empty-versus-single `BindingsSet` distinction (`BindingsSet([])` = failure,
`BindingsSet([∅])` = trivial success) is subtle; the developers flag the
existing names as potentially misleading.

`hyperon-atom/src/matcher.rs:519`:
`// TODO: can we use binding deps instead of var deps?` in `narrow_vars`.
Dependency tracking for variable narrowing may be coarser than necessary.

---

## 3. Minimal MeTTa Interpreter (`lib/src/metta/interpreter.rs`)

The embedded ops (`eval`/`chain`/`unify`/`cons-atom`/`decons-atom`/`function`/
`collapse-bind`/`superpose-bind`, declared at `interpreter.rs:378-389`) and
their handlers (`FUNCTION`/`UNIFY`/`CONS_ATOM`/`DECONS_ATOM`/`SUPERPOSE_BIND`/
`COLLAPSE_BIND`/`RETURN`, at approximately `interpreter.rs:805-1070`) contain
only defensive invariant guards. The developer-intent markers for the
interpreter are in the type-directed driver and call glue:

### Conflict between the type-analysis phase and `eval` re-dispatch

`lib/src/metta/interpreter.rs:1601-1609`:

```
// TODO: At the moment metta_call() is called we already know
// should we call atom as a tuple or as a function.
// But (eval (<op> <args>)) inside independently decides whether it
// should call grounded operation <op>, or match (= (<op> <args>) <res>).
// This can lead to the conflict if user defines a function using
// grounded atom (for instance (+3 1 2 3)) and after type analysis
// interpreter decides we need to match it then calling eval will
// analyze the expression again and may call grounded op instead of
// matching.
```

The type-analysis phase (`interpret_expression`) decides whether an expression
should be treated as a tuple or a function call, but `eval` re-derives this
decision independently. The two decisions can disagree, particularly when a
user redefines a grounded operation via `=`. This is the primary semantic
caveat for a formalization of `eval`/`metta`/`metta-call`.

The Lean formalization addresses this by deciding dispatch once from the
operator's signature (`argMask`/`returnsAtom`), so the type phase and the
evaluation step are consistent by construction.

### Expression return-type forced to `%Undefined%`

`lib/src/metta/interpreter.rs:1313-1322`:

```
// TODO: it is a hack to prevent Expression working
// like Atom return type. On the one hand we could
// remove old code to prevent Atom results being
// interpreted after the fix of return type-check
// on the other hand may be it is logical to make
// Expression have the same semantics. It would be
// useful to provide the manner to execute funciton
// body before returning the Atom (or Expression)
// as is.
```

followed by `if ret_type == ATOM_TYPE_EXPRESSION { ret_type = ATOM_TYPE_UNDEFINED; }`
at `interpreter.rs:1322-1323`. A function whose declared return type is
`Expression` has that type silently replaced with `%Undefined%` so its result
is still interpreted. The developers are explicit that this is a workaround; the
intended semantics is not settled. The Lean formalization addresses the same
concern via the `returnsAtom` static return-type gate, derived from each
function's declared signature with no mutable state.

### Variable-operator hotfix

`lib/src/metta/interpreter.rs:721-726`:

```
// TODO: This is a hotfix. Better way of doing this is adding
// a function which modifies minimal MeTTa interpreter code
// in order to skip such evaluations in metta-call function.
```

This guards `is_variable_op` and returns `not-reducible` for expressions whose
operator is a variable (`($f x)`). The principled fix, as the comment notes,
belongs in the `metta-call` layer. The Lean formalization provides a total,
documented `isVariableHeaded` guard that implements the "better way" the
comment describes.

### `ExecError::NoReduce` as control flow

`lib/src/metta/interpreter.rs:658-660`:

```
// TODO: we could remove ExecError::NoReduce and explicitly
// return NOT_REDUCIBLE_SYMBOL from the grounded function instead.
```

`ExecError::NoReduce` is used as a control-flow signal; the developers prefer
an explicit `NotReducible` atom returned by grounded operations. This affects
the contract between `eval` and grounded operations.

### Formal-argument variable handling on function entry

`lib/src/metta/interpreter.rs:681-686`:

```
// TODO: we could instead add formal argument variables of the called
// functions into stack.vars collection. One way of doing it is getting
// list of formal var parameters from the function definition atom
// but we don't have it returned from the query. Another way is to
// find all variables equalities in bindings with variables
// from call_stack.vars.
```

The current treatment of formal versus actual argument variables on function
entry is a workaround (`apply_and_retain`). The cleaner design would track
formal parameter variables explicitly. The Lean formalization realises
`apply_and_retain` as continuation-scoped retention with transitive solution
resolution (`resolveAtom`), which is what passes `b2`'s recursive backchaining.

### Grounded-atom extraction for `collapse-bind`/`superpose-bind`

`lib/src/metta/interpreter.rs:1052-1054`:

```
// TODO: cloning is ineffective, but it is not possible
// to convert grounded atom into internal value at the
// moment
```

In `atom_into_bindings`, used by `collapse-bind` and `superpose-bind`,
extracting a value from a grounded atom requires cloning because no move-out
API exists. A performance concern with an API design implication.

### Stack representation notes (implementation level)

`interpreter.rs:59`: `// TODO: Try representing Option via Stack::Bottom`.
`interpreter.rs:63`: `// TODO: Could it be replaced by calling a return handler when setting the flag?`
on the `finished` flag.
`interpreter.rs:106`: `// TODO: should it be replaced by Iterator implementation?` on `Stack::fold`.
These are implementation-level cleanup notes with no semantic consequence.

### Migration state of the runner

`lib/src/metta/runner/mod.rs:694`:
`// TODO: I think we may be able to remove the 'interpreter lifetime after the minimal MeTTa migration`.

`lib/src/metta/runner/mod.rs:1176`:
`/// FUTURE-CLEANUP-TODO: I would like to be able to delete this Executable type ... by making the runner's only instructions be a stream of atoms.`

These indicate the intended end-state: a runner whose only instruction is a
stream of atoms, with everything expressed in minimal MeTTa.

---

## 4. Spaces and Modules

> Note: `lib/src/metta/runner/stdlib/core.rs`, which implements `function`/`return`,
> `get-type`, `type-cast`, `unify`, `quote`/`unquote`, `sealed`, `eval`,
> `case`/`switch`, was surveyed and contains no semantic developer-intent
> markers. The interpreter-level caveats are in section 3.

### Spaces: indexing and query

`hyperon-space/src/lib.rs:206-212`: `Space::visit` is an optional trait method;
spaces may legitimately not implement it (the documentation says "Return Err(())
if method is not implemented"). This drives runtime failures in several stdlib
operations.

`lib/src/metta/runner/stdlib/space.rs:598`: `get-atoms` returns
`ExecError::Runtime("Unsupported Operation. Can't traverse atoms in this space")`
when `visit` is not implemented. Some spaces are not enumerable.

`lib/src/metta/runner/stdlib/space.rs:99-101, :140-143`: `fork-space` supports
only `GroundingSpace`/`MorkGroundingSpace`; `mork-symbolic-snapshot` requires a
MORK-backed space. Other space types are rejected at runtime with "Unsupported
Operation".

`hyperon-space/src/index/trie.rs:314-315`:
`// FIXME: should we check !is_hashable here?`: a potentially missing guard in
the equality-match query path for non-hashable keys.

`hyperon-space/src/index/trie.rs:186-189`:
`// TODO: Ability to remove hashable keys is to be added...`: deletion of
hashable keys from the trie index is incomplete.

`hyperon-space/src/index/storage.rs:77-79`:
`// TODO: calling Grounded::serialize() is a workaround. We don't know in
advance whether atom is serializable...`: serializability is detected by
attempting serialization rather than a declared capability, affecting how
grounded atoms are indexed.

`hyperon-space/src/index/mork.rs:1-7` (module doc) and `mork_encoding.rs:47/62-63/142`:
Atoms that cannot be encoded to MORK bytes remain queryable via a slower
correctness path but are not covered by the MORK byte fast path. The design
is intentionally two-path; query results must agree across both.
`UnsupportedGroundedAtom` is the named error variant.

`hyperon-space/src/index/trie.rs:271`:
`// TODO: write an algorithm which returns an iterator instead of collected result`
in `query_internal` (eager collection; performance and lazy-result semantics).

`lib/src/space/module.rs:44`:
`panic!("Only ModuleSpace is expected inside dependencies collection")`: a
core-query-path invariant enforced by panic rather than a typed error.

The Lean formalization models spaces as a pure threaded `World` (named spaces
plus a state store plus token bindings), sequenced through evaluation. The
first-argument (head) indexing rule (`MinEnv.ruleIndex`) is proved sound
(`matchAtoms_headKey`, `Indexing.lean`): no firing rule is ever omitted.
Query completeness is a theorem rather than an empirically tested property.

### Module system: semantics explicitly provisional

`lib/src/metta/runner/stdlib/module.rs:40-66` contains a long `//QUESTION`
block noting that `import!` means three different things: import all to `&self`,
import as a named symbol, and import a specific item from a module. The comment
reads in part: "For now, in order to not lose functionality, I have kept this
behavior." One behavior (`import_item_from_dependency_as`) exists in the code
but is not yet wired up: "isn't called yet because I wanted to discuss the way
to expose it." Module import semantics are noted as unsettled.

`lib/src/metta/runner/stdlib/module.rs:27-29`:
`//TODO: Ideally the "import as" / "import into" part would be optional`.

`lib/src/metta/runner/stdlib/module.rs:88-91`:
`//TODO: Currently this pattern is unreachable on account of arity-checking...
but I have the code path in here for when it is possible`: a dead `import!`
branch kept for a future arity model.

`lib/src/metta/runner/stdlib/module.rs:136-139`:
`//NOTE: ... include ... results prior to the last are dropped. I don't know
how to fix this or if it's even wrong...`: `include` drops all but the final
sub-evaluation's results; the author notes uncertainty about whether this is
correct.

`lib/src/metta/runner/modules/mod_names.rs:298-307`:
`panic!("Need Polonius or Rust 2024 edition")`: the mutable module-name-tree
lookup (`name_to_node_mut`) is entirely stubbed with a panic pending a
borrow-checker feature. The function is marked `#[allow(dead_code)]`.

`lib/src/metta/runner/pkg_mgmt/catalog.rs:35-39`:
`//LP-TODO-NEXT make a test to make sure circular imports are caught and don't
lead to infinite recursion` and `//QUESTION: Should circular imports between
modules be allowed?`: circular imports are currently disallowed (no forward
declaration), and the guard against infinite recursion is untested.

`lib/src/metta/runner/modules/mod.rs:554`: module loaders may load only
sub-modules, not arbitrary modules (enforced as a hard error).

`lib/src/metta/runner/modules/mod.rs:769-770, :833-837`:
`//LP-TODO-NEXT` notes missing tests for nested sub-module loading and for error
propagation when an inner loader fails (the expected behavior: a failed inner
load should leave neither module in the index, unverified).

`lib/src/metta/runner/modules/mod.rs:648, :650`:
`ResourceKey::Authors` / `::Description` are declared but marked `**TODO**`,
not parsed.

`lib/src/metta/runner/stdlib/module.rs:196`: the module-listing operation is
described as "a temporary stop-gap".

Package management (provisional, blocked features):
`catalog.rs:576-577` (no `.metta` package-info, blocked on Atom-Serde);
`:590-591` (no filename sanitization for module names);
`managed_catalog.rs:194-197` (cannot substitute a compatible module version;
the "Requirement API" is not built);
`managed_catalog.rs:82/91/113` (catalog API subject to change; dependency-tree
tracking unimplemented);
`package.rs:43-46/85-88` (`register-module!`/`git-module!` omit rename and
branch-name options, blocked on varargs);
`git_cache.rs:26/131/175` (read-only without the `git` feature; corrupt cache
results in a fatal panic).

---

## 5. Standard Library Grounded Operations

`lib/src/metta/runner/stdlib/space.rs:510-511`:
`// TODO: when grounded atom will be able returning few types then
// all types should be returned`: `new-state` (StateMonad) reads only the
first type from a type list; multi-typed state is silently truncated. The root
cause is the single-value `Grounded::type_()` noted in section 1.

`lib/src/metta/runner/stdlib/space.rs:652`:
`// TODO? Is it necessary to distinguish whether the atom was removed or not?`
`remove-atom` always returns unit, discarding the boolean of whether anything
was actually removed. This is a semantic gap with observable consequences for
programs that need to test removal.

`lib/src/metta/runner/stdlib/mod.rs:74-80`: `&self` is wired into the stdlib
via a strong `Atom::gnd(space.clone())`, creating a self-reference that is
never freed. Two proposed fixes are noted (weak pointer; resolve `&self` inside
`GroundingSpace::query`) but not yet implemented. The extra-args mechanism at
`mod.rs:64-65` is separately called "a temporary hack" (issue #410).

`stdlib.metta:367-370`: the `->` type constructor has no type definition and
matches only via `%Undefined%` (cross-listed from section 1, as it affects
runtime behavior as well as the type system).

`stdlib.metta:617-618`: no variadic operations; `nop` is hand-defined for 0
and 1 arguments.

`stdlib.metta:626`: `empty` is redundant with the `Empty` atom but kept for
compatibility.

`stdlib.metta:773, :1352, :1358`: `help!` produces duplicate output, causes a
segfault on `&self`, and fails for operations defined in both Python and Rust
(`+ - * / % < > <= >= ==`).

`lib/src/metta/runner/stdlib/atom.rs:718`: documents a previously corrected
bug in `unique`/dedup (earlier versions dropped structurally distinct atoms).

`lib/src/metta/runner/stdlib/arithmetics.rs:52,94,134,252`:
`panic!("Unexpected state")` after argument-type checks (hard panic rather than
a typed error return).

Built-in modules (performance or composability concerns):
`random.rs:17-21`: `random-int`/`random-float` can hang on oversized ranges,
deferred to `rand` 0.9+;
`json.rs:234`: `u64` values are not supported;
`catalog.rs:99/164/224`: catalog listings print to stdout rather than
returning atoms, and are therefore not composable within MeTTa programs.

---

## 6. Other Markers

`hyperon-atom/src/lib.rs:803-806`:
`// TODO: it is not clear whether this step really improves performance.`
(downcast fast-path in `as_gnd`). Performance observation only.

`hyperon-atom/src/iter.rs:16`:
`// TODO: Single/Expression enum can be used inside to make code more clear.`
Cosmetic.

`hyperon-atom/src/gnd/number.rs:15`:
`// TODO: this promoting is helpful ...` (numeric promotion). Minor.

`hyperon-atom/src/serial.rs:35`:
`Serialization of the type is not supported by serializer.` (error variant
documentation).

`hyperon-atom/src/lib.rs:302`:
`// TODO: for now name() is used to expose keys of Bindings via C API ...`
(C-API shim).

### Runner-core planned refactors (`lib/src/metta/runner/mod.rs`)

`mod.rs:57`: `//LP-TODO-NEXT: This description above is correct, but it's not
complete.` (module design documentation out of date).

`mod.rs:515, :640, :694, :745-754`: a cluster of planned refactors including
removing `RunnerState` from the public API and simplifying the step loop and
`'interpreter` lifetime after the minimal-MeTTa migration.

`mod.rs:1176-1179`: `FUTURE-CLEANUP-TODO`: the developers want to delete the
`Executable` type and make the runner's only instructions a stream of atoms,
blocked by the need to dispatch one-off Rust functions during module loading.

`mod.rs:720/725/874/1221/246`: runner lifecycle invariants enforced via
`panic!` (module must exist and be initialized; initialization-file read failure
is fatal).

`environment.rs:404/411`: `#includePath` and `#gitCatalog` directives silently
degrade to warnings when the `pkg_mgmt` feature is absent; `:192` contains a
builder-order panic; `:395/:475` note future serialization and format-library
cleanups.

---

## Summary: Where a Machine-Checked Reference Adds Value

The five areas where the Hyperon source itself signals the most open design work
are the following, and they correspond directly to the formal properties this
Lean development establishes:

1. **Separating tuple from function-application in typing** and replacing the
   overloaded `Vec`-emptiness return convention (`types.rs:494-512`). The Lean
   formalization makes this distinction explicit in `argMask`/`returnsAtom`
   dispatch, decided once from the operator's signature.

2. **Assigning a type to `->` and other type constructors; supporting variadic
   types** (`stdlib.metta:367-370`, `:617-618`). The current `%Undefined%`
   fall-through is the central soundness gap in the gradual type system. The
   type-checker faithfulness theorems (`TypeSoundness.lean`) characterize the
   actual permissive behavior precisely.

3. **Resolving the tuple-vs-function and grounded-call-vs-match conflict between
   the type phase and `eval`** (`interpreter.rs:1601-1609`) and removing the
   `Expression` return-type override (`interpreter.rs:1313-1323`). These define
   the actual operational semantics of `metta`/`metta-call`/`eval`. The Lean
   formalization addresses both by deriving dispatch statically from each
   function's declared type.

4. **Principled handling of `Variable ~ Grounded` unification** rather than the
   current single-branch choice (`matcher.rs:1105-1108`), and multi-valued
   `Grounded::type_()` for type non-determinism (`hyperon-atom/src/lib.rs:419-421`).
   Both affect the matching and typing relations that a proof layer must state.
   The Lean formalization's first-argument indexing is proved sound
   (`matchAtoms_headKey`, `Indexing.lean`).

5. **Tightening meta-type checking** so that `Atom`/`Expression` meta-types do
   not mask ill-typed atoms (`types.rs:1177/1225/1298`, `check_meta_type` at
   `types.rs:615`), and adding type-variable inference for variables
   (`types.rs:379-385`). The Lean type-checker faithfulness proofs
   (`TypeSoundness.lean`) characterize the permissive behavior exactly, giving
   a precise statement of what the implementation currently does and what a
   tighter checker would need to change.
