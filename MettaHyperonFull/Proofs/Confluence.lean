import MettaHyperonFull.Proofs.Basic

/-!
# Metatheory: confluence of the deterministic fragment

MeTTa's reduction is *intentionally nondeterministic*: a configuration can step to several
successors (e.g. `(superpose (1 2))` reduces to both `1` and `2`, which are distinct normal forms),
so the reduction **relation is not globally confluent**: there is no unique normal form, and that
is a feature, not a bug. Our abstract machine reflects this directly: one step
(`interpretStack1`) returns a *list* of successor configurations.

What *is* true, and what matters for MeTTa's intended on-chain / smart-contract use, is that the
machine is **deterministic as a function** (`Proofs/Results.lean`), and consequently its
**deterministic fragment**, the sub-relation in which a configuration has exactly one successor,
is **confluent** (Church–Rosser). So wherever a computation does not branch, its result is
independent of the evaluation order: it is replayable. Determinism ⇒ confluence, made precise:

* `deterministic_confluent`: a general rewriting lemma: any functional (deterministic) one-step
  relation is confluent.
* `Minimal.DetStep` / `Minimal.detStep_functional` / `Minimal.detStep_confluent`: the single-
  successor step relation of `interpretStack1` is functional (because `interpretStack1` is a total
  function), hence confluent.

The non-confluent, branching part of the relation is exactly the explicit nondeterminism
(`superpose`, multiple matching rules); it is reified in the result list rather than hidden in the
transition relation.
-/

open Relation

namespace Metta

/-- A deterministic (functional) one-step relation is confluent (Church–Rosser): if every element
steps to at most one successor, any two reduction sequences from a common start can be rejoined.
The branching of a relation is the *only* obstruction to confluence. -/
theorem deterministic_confluent {α : Type*} {R : α → α → Prop}
    (hdet : ∀ {x y z : α}, R x y → R x z → y = z) {a b c : α}
    (hab : ReflTransGen R a b) :
    ReflTransGen R a c → ∃ d, ReflTransGen R b d ∧ ReflTransGen R c d := by
  induction hab generalizing c with
  | refl => exact fun hac => ⟨c, hac, ReflTransGen.refl⟩
  | @tail b' b hab' hstep ih =>
      intro hac
      obtain ⟨d, hbd, hcd⟩ := ih hac
      rcases hbd.cases_head with rfl | ⟨x, hb'x, hxd⟩
      · -- `hbd` was reflexive (d = b'): then `c →* b' → b`.
        exact ⟨b, ReflTransGen.refl, hcd.tail hstep⟩
      · -- head step `b' → x →* d`; determinism forces `b = x`, so `b →* d`.
        obtain rfl := hdet hstep hb'x
        exact ⟨d, hxd, hcd⟩

namespace Minimal

/-- A deterministic step of the abstract machine: a configuration `(it, st)` whose interpreter step
yields EXACTLY one successor `(it', st')`. Branching steps such as `superpose` or multiple matching rules
return a longer list and are excluded; that is the irreducible nondeterminism of MeTTa. -/
def DetStep (env : MinEnv) (fuel : Nat) (p q : Item × St) : Prop :=
  interpretStack1 env fuel p.2 p.1 = ([q.1], q.2)

/-- `DetStep` is functional: `interpretStack1` is a total function, so a configuration has at most
one deterministic successor. -/
theorem detStep_functional (env : MinEnv) (fuel : Nat) {p q1 q2 : Item × St}
    (h1 : DetStep env fuel p q1) (h2 : DetStep env fuel p q2) : q1 = q2 := by
  have h := h1.symm.trans h2
  simp only [List.cons.injEq, and_true, Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2

/-- **The deterministic fragment of the abstract machine is confluent (Church–Rosser).** Where
MeTTa evaluation does not branch, the result is independent of evaluation order, which is the replayability
an on-chain VM requires. -/
theorem detStep_confluent (env : MinEnv) (fuel : Nat) {p b c : Item × St}
    (hab : ReflTransGen (DetStep env fuel) p b)
    (hac : ReflTransGen (DetStep env fuel) p c) :
    ∃ d, ReflTransGen (DetStep env fuel) b d ∧ ReflTransGen (DetStep env fuel) c d :=
  deterministic_confluent (R := DetStep env fuel)
    (fun h1 h2 => detStep_functional env fuel h1 h2) hab hac

end Minimal
end Metta
