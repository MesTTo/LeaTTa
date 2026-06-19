/-
LeaTTa: Chapter: The future-work branch and the roadmap.
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

#doc (Manual) "The future-work Branch" =>
%%%
tag := "sec-future"
%%%

The development has two branches. The `metatheory` branch covers MeTTa as it stands today: the
minimal-MeTTa kernel and standard library, validated against Hyperon's corpus, with the full
machine-checked metatheory and no `sorry`. The `future-work` branch prototypes the directions the
minimal-MeTTa specification itself lists under "future work", together with a fuller module system. A
feature is admitted to the branch only once the metatheory still goes through, or its interaction
with the metatheory is documented precisely.

# A Feature, and a Finding

The first feature on the branch is match-by-equality, written `(:= x)`, which the specification
lists as "syntax to match an atom by equality". Inside `unify`, the pattern `(:= x)` matches by
structural equality rather than by unification: the `then` branch is taken exactly when the queried
atom equals `x` under the current bindings, and no new variable bindings are produced.
`(unify $a (:= Empty) then else)` therefore takes the `else` branch for a free `$a`, whereas
ordinary `unify` would bind `$a` to `Empty`. The feature is implemented in `unifyOp`, and the full
build passes the corpus at 270 of 270.

The feature was first prototyped not in `unify` but in the general matcher `matchAtomsWith`, and
the machine-checked proofs caught a design problem. A `(:= x)` left-hand side can fire on a query
with a different head, so such a rule no longer belongs in its head's first-argument-indexing bucket.
This contradicts the indexing-soundness theorem of {ref "sec-meta"}[the metatheory]
(`matchAtoms_headKey`, "matching forces head agreement"). Preserving the theorem would require either
bucketing by the head of `x` (sound only when `x` is symbol-headed) or treating every `(:= x)` rule
as head-less (sound, but skipping indexing for those rules). The specification's intended feature, a
modifier scoped to `unify`, avoids the problem entirely. The proofs caught this before any test did.

# The Roadmap

The branch records the remaining items from the specification's future-work section, each annotated
with its interaction with the existing metatheory.

 * *Gap matching* `(A ... D ...)`, which matches part of an expression with holes. Like `(:= x)`,
   this is a matcher-level feature whose interaction with first-argument indexing must be worked out,
   since a gap pattern's head may not determine its bucket.
 * *Explicit atomspace variable bindings*, making the interpreter's implicit bindings explicit
   everywhere. Per the specification this would allow `eval` to be defined in terms of `unify`,
   enabling user-programmable chaining strategies. It requires a deep refactor of the interpreter
   core.
 * *General matching modifiers* `(:mod atom)`, the specification's proposed syntax for adding
   matching directives, of which `:=` is the first, without clashing with user symbols.
 * *A fuller module system*. Beyond the namespaced `import!` and `register-module!` already on the
   `metatheory` branch, this covers the `import * from`, `import as`, and `import item from` forms,
   package metadata with version selection, and the catalog-management operations.
