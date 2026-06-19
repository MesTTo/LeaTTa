# Structural correspondence with a sibling K-Framework sketch

What is authoritative here. Faithfulness of this Lean kernel is anchored on Hyperon itself.
`scripts/run-oracle.sh` runs Hyperon's own, unmodified test corpus and passes 270 of 270
(`tests/corpus/`), and the kernel is written against
`hyperon-experimental/lib/src/metta/interpreter.rs`. That empirical agreement, together with the
machine-checked proofs in `MettaHyperonFull/Proofs/`, is the real evidence.

What this document is. Alongside the Lean work, the same author maintains an independent K-Framework
sketch, `metta-elegant.k`, a recreation of a CASL algebraic specification `MettaElegant.casl`. It is
an in-progress, AST-level rewriting sketch rather than an authoritative reference, and it may simplify
or diverge from Hyperon in places. It is included here only as a structural cross-check: two
independently written encodings landing on the same shape of rewrite system is some extra evidence
that the shape is the standard one. Where the K sketch and Hyperon would disagree, Hyperon and the
270-assertion corpus govern.

None of the Lean proofs depend on the K sketch being correct; the table is only a reading aid.

## The shared shape

| concept | K sketch (`metta-elegant.k`) | Lean (`MettaHyperonFull/`) |
|---|---|---|
| atoms | `sym`/`var`/`ground`/`expr` (l.16–19) | `Atom.sym`/`.var`/`.gnd`/`.expr` (`Core/Atom.lean`) |
| substitution | `subst(Σ, –)` structural (l.110–138) | `Subst.apply` / `instantiate` |
| matching | `matchAtom` case split, both var orientations (l.151–157) | `matchAtomsWith` / `matchAtoms` (`Core/Matching.lean`) |
| `chain` (monadic bind) | `chain(A,X,B) => subst(bindSubst(X,A),B)` (l.334) | `chain` frame + `instantiate` |
| `unify` | l.316–319 | `unify` embedded op |
| `cons`/`decons-atom` | l.313–314 | `Builtins.consAtom`/`deconsAtom` |
| `function(return A) => A` | l.311 | `Ret.function` + `evalResult` |
| `superpose` spread | l.321–323 | `superposeOp` |
| `metaType` to Symbol and friends | l.342–347 | `getMetatypeOp` |
| `bad-arg-type`/`error` | l.53–55 | `(BadArgType …)`/`(Error …)` |

## Equality rewriting, where a Lean proof is the real content

This is the one place that is more than a reading aid. A naive minimal-MeTTa semantics rewrites by
scanning the whole space linearly for a matching `(= L R)`, which is exactly what the K sketch does:

```
rule evalScan(space-cons(eq(L, R), _), Input) => subst(mgu(L, Input), R)
  requires unifiable(L, Input)                                  // metta-elegant.k  l.234
```

The Lean kernel instead consults a head-keyed index (`MinEnv.candidates`, first-argument indexing),
and `Proofs/IndexingComplete.lean` proves the index returns exactly the linear scan's result:

* `candidates_sound`: every candidate is a genuine `=`-rule, so the indexed set is contained in the
  scan.
* `candidates_complete`: every rule whose `L` unifies with `Input` is a candidate, so the indexed set
  contains the scan.

This theorem is about indexed evaluation versus the textbook linear scan in general. It stands on its
own and does not rely on the K sketch. The K rule above is just a concrete picture of the linear-scan
side. This is the same-head regime where Hyperon's own `Space::visit` undercounts (issue #1079); here
completeness is machine-checked.

## One deliberate representation difference

The K sketch leans on K's `--search` for nondeterminism (`collapse(A) => expr(A)`, l.328, with the
search at the meta-level). The Lean kernel reifies nondeterminism into the result list, so evaluation
is a deterministic function (`Proofs/Results.lean`, which is the replayability an on-chain use needs),
which is also why it matches Hyperon's explicit comma-tuple `collapse`. The two give the same set of
results, with an inter-derivable difference in where the search lives.
