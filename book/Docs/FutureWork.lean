/-
LeaTTa: Chapter: future work and the roadmap.
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

#doc (Manual) "Future Work" =>
%%%
tag := "sec-future"
%%%

This chapter records directions that are not part of the 1.0 release contract. Some have small
prototypes; some are only scoped. A feature belongs in the main development only once the existing
metatheory still checks, or once its interaction with the metatheory is stated precisely.

# A Feature, and a Finding

The first feature on the branch is match-by-equality, written `(:= x)`, which the specification lists as "syntax to match an atom by equality". Inside `unify`, the pattern `(:= x)` matches by structural equality rather than by unification: the `then` branch is taken exactly when the queried atom equals `x` under the current bindings, and no new variable bindings are produced. So `(unify $a (:= Empty) then else)` takes the `else` branch for a free `$a`, whereas ordinary `unify` would bind `$a` to `Empty`. The feature is implemented in `unifyOp`, and the full build passes the corpus at 270 of 270.

The feature was first prototyped not in `unify` but in the general matcher `matchAtomsWith`, and the machine-checked proofs caught a design problem. A `(:= x)` left-hand side can fire on a query with a different head, so such a rule no longer belongs in its head's first-argument-indexing bucket. This contradicts the indexing-soundness theorem of {ref "sec-meta"}[the metatheory] (`matchAtoms_headKey`, "matching forces head agreement"). Preserving the theorem would require either bucketing by the head of `x` (sound only when `x` is symbol-headed) or treating every `(:= x)` rule as head-less (sound, but skipping indexing for those rules). The specification's intended feature, a modifier scoped to `unify`, avoids the problem entirely. The proofs caught this before any test did.

# The Roadmap

The remaining items below come from the minimal-MeTTa specification and from the gaps exposed by the
formalization. Each item is listed with the proof obligation it creates.

 * *Gap matching* `(A ... D ...)`, which matches part of an expression with holes. Like `(:= x)`,
   this is a matcher-level feature whose interaction with first-argument indexing must be worked out,
   since a gap pattern's head may not determine its bucket.
 * *Explicit atomspace variable bindings*, making the interpreter's implicit bindings explicit
   everywhere. Per the specification this would allow `eval` to be defined in terms of `unify`,
   enabling user-programmable chaining strategies. It requires a deep refactor of the interpreter
   core.
 * *General matching modifiers* `(:mod atom)`, the specification's proposed syntax for adding
   matching directives, of which `:=` is the first, without clashing with user symbols.
 * *A fuller module system*. Beyond the namespaced `import!` and `register-module!` already present,
   this covers the `import * from`, `import as`, and `import item from` forms, package metadata with
   version selection, and the catalog-management operations.
