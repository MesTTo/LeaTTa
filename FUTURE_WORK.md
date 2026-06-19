# Future work (the `future-work` branch)

The `metatheory` branch is MeTTa as it stands today: the faithful minimal-MeTTa kernel and standard
library, validated 270/270 against Hyperon's own corpus, with the machine-checked metatheory layer
(determinism, confluence, sound and complete first-argument indexing, gradual-type soundness
including grounded-core preservation and subject reduction over user `=`-rewriting, and
α-equivalence), at 0 `sorry`.

This branch prototypes the directions that the minimal-MeTTa specification itself lists under future
work, together with a fuller module system. Each prototype is kept honest: a feature lands only with
the metatheory intact, or its interaction with the metatheory is documented.

## Implemented on this branch

### Match-by-equality `(:= x)` (spec: "Syntax to match atom by equality")

`(unify <atom> (:= x) then else)` matches by structural equality. The `then` branch is taken iff
`atom` equals `x` under the current bindings, with no new variable bindings. So
`(unify $a (:= Empty) then else)` takes `else` for a free `$a`, where ordinary `unify` would bind
`$a` to `Empty`. It is implemented in `unifyOp` (`Minimal/Interpreter.lean`), the full build is green,
and the corpus is 270/270.

Why it is scoped to `unify`, and a metatheory finding worth the Hyperon team's attention. The
specification frames `:=` as a `unify`-pattern modifier, so that is its correct home. The feature was
first prototyped in the general matcher (`matchAtomsWith`) instead, and the machine-checked metatheory
caught a genuine design problem. A `(:= x)` left-hand side can fire on a query with a different head,
so it no longer lives in that head's first-argument-indexing bucket, which contradicts the
indexing-soundness theorem `Proofs/Indexing.lean : matchAtoms_headKey` ("matching forces head
agreement"). To keep the theorem, a general-matcher `:=` would force one of two changes: either
`headKey` sees through `:=` and buckets by the head of `x`, which is sound only when `x` is
symbol-headed, or every `(:= x)` rule is treated as head-less (`varRules`, always a candidate), which
is sound but defeats indexing for those rules. The specification's intended feature, a `unify`
modifier, needs neither. The lesson is that the proofs are not decoration: they pin down a feature's
correct scope.

## Planned (specification future work and modules)

- Gap matching `(A ... D ...)`, which matches part of an expression with holes (spec: "Syntax to
  match part of the expression"). This is a matcher-level feature, and like `:=` its interaction with
  first-argument indexing must be worked out, since a gap pattern's head may not determine its bucket.
- Explicit atomspace variable bindings: make the interpreter's implicit bindings explicit everywhere.
  Per the specification this would let `eval` be defined in terms of `unify`, enabling
  user-programmable chaining strategies. It is a deep refactor of the interpreter core.
- General matching modifiers `(:mod <atom>)`, the specification's proposed escape for adding matching
  directives, of which `:=` is the first, without clashing with user symbols.
- A fuller module system. Beyond `register-module!` and namespaced `import!`, already on
  `metatheory`, this covers `import * from`, `import as`, and `import item from`, `_pkg-info.metta`
  package metadata with version selection, and the catalog-management operations `catalog-list!`,
  `catalog-update!`, and `catalog-clear!`.

## References

- `minimal-metta.md` (Minimal MeTTa specification): the instruction set and the future-work section.
- `metta.md` (MeTTa language specification): the full `metta`/`type_cast`/`interpret_*` algorithm this
  kernel implements.
- Hyperon module documentation: `register-module!`, the `top:mod:sub` name-path hierarchy,
  `ModuleCatalog` and `DirCatalog`, and the `catalog-*!` operations.
