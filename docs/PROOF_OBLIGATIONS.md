# Proof obligations

The project includes executable definitions where feasible and formal theorem targets where the full proof is large or implementation-dependent.

## Core metatheory

1. Substitution preserves well-formedness.
2. Substitution is identity on atoms with no variables in its domain.
3. Occurs-check prevents cyclic substitutions.
4. Unification soundness: if `unify p t = σ`, then `σ p = σ t`.
5. Pattern matching soundness: every returned binding instantiates the query pattern to the matched atom.
6. Alpha-equivalence is reflexive, symmetric, transitive and compatible with substitution modulo capture conditions.

## Type and equality metatheory

1. `(: a T)` loading extends the type environment monotonically.
2. Arrow-type application preserves declared result type under argument checking.
3. Equality rules are directional and need not be symmetric.
4. Equality-based evaluation preserves well-formedness.
5. Static type checking is intentionally weaker than equality inference; equality inference belongs to the interpreter loop.

## Operational semantics

1. Small-step transition preserves well-formed machine states.
2. Runtime `runFuel` refines the relational small-step semantics for bounded traces.
3. Immediate evaluation `!a` is observationally equivalent to adding `a` to the input register rather than the knowledge register.
4. `transform P T` equals pattern matching followed by substitution into `T`.
5. `match` over the current space agrees with the matching relation.
6. Grounded host calls are sound relative to their declared contracts.
7. Distributed/DAS matching is sound relative to local-space matching when remote access is complete; otherwise it is an under-approximation.

## Metagraph rewriting

1. Expression-to-DAG encoding is well-formed.
2. Homomorphisms preserve target order and labels modulo type inheritance/enrichment homomorphism.
3. SPO rewrite patch preserves metagraph well-formedness under the stated domain/codomain conditions.
4. DPO rewrite patch preserves metagraph well-formedness under gluing/dangling-edge conditions.
5. MeTTa matching can be simulated by metagraph homomorphism plus VBTO/substitution.
6. Operational MeTTa steps can be encoded as metagraph rewrite steps.

## Reflection and traces

1. Quotation/unquotation round-trip for closed atoms.
2. Adding/removing atoms implements self-modification at the object-language level.
3. Trace encoding preserves step order.
4. Bisimulation between MeTTa operational traces and metagraph rewrite traces.
5. Higher-order program manipulation forms an iterated trace/program transformation structure; the Ruliad/topos layer is represented as a target interface, not as a completed HoTT formalisation.

## Further proof directions

These extend the proved metatheory and are not yet formalised.

1. Deeper preservation. Two generalisations of `Preservation.lean`, available now that the gradual consistency relation is in hand (`Gradual.lean`): thread consistency `~` through the typing judgement in place of the current subtyping-top supertype rule, and support polymorphic and dependent rules, where the substitution threads through type arguments as well, for example `(Cons $x $xs)`.
2. Reflection. Lift the fixed-signature assumption to a space-indexed judgement, for rules that rewrite `:` and `<:` facts themselves.
