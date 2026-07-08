-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.Newman
Layer: Proofs
Purpose: Newman's lemma and its application to the runtime's reduction relation. Abstractly, a
  terminating, locally confluent relation is confluent (Huet's well-founded induction over the step
  relation). Specialised to `RewStep`: when a measure strictly decreases on every step (termination)
  and the system is locally confluent, the one-step rewrite relation is confluent, so normal forms are
  unique. Together with `eval_computes_normal_of_measure`, this gives the conditional completeness of
  the runtime: it computes the unique normal form.
Imports: Mathlib.Logic.Relation, CordialMiners-style; MeTTaIL.Semantics.Context
Trusted boundary: none (fully proved)
Main exports: Joinable, LocallyConfluent, Confluent, newman, rewStep_confluent_of_measure
Open obligations: deciding local confluence by critical-pair analysis is the remaining step toward an
  automatic confluence check.
-/
import Mathlib.Logic.Relation
import MeTTaIL.Semantics.Context

namespace MeTTaIL

open Relation

variable {α : Type*}

/-- Two elements are joinable when they reduce to a common element. -/
def Joinable (r : α → α → Prop) (a b : α) : Prop :=
  ∃ c, ReflTransGen r a c ∧ ReflTransGen r b c

/-- Joinability is symmetric. -/
theorem Joinable.symm {r : α → α → Prop} {a b : α} (h : Joinable r a b) : Joinable r b a :=
  ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩

/-- Local confluence (weak Church-Rosser): every one-step divergence is joinable. -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → Joinable r b c

/-- Confluence (Church-Rosser): every many-step divergence is joinable. -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → Joinable r b c

/-- Newman's lemma: a terminating, locally confluent relation is confluent. The termination hypothesis
    is that the step relation is well-founded read backwards (no infinite reduction). Proof by
    well-founded induction over reduction, completing the local-confluence diamond and recurring on the
    two reducts (Huet 1980). -/
theorem newman (r : α → α → Prop) (hwf : WellFounded (fun b a => r a b))
    (hlc : LocallyConfluent r) : Confluent r := by
  intro a
  refine hwf.induction
    (C := fun a => ∀ b c, ReflTransGen r a b → ReflTransGen r a c → Joinable r b c) a ?_
  intro a ih b c hab hac
  obtain rfl | ⟨a1, ha1, ha1b⟩ := hab.cases_head
  · exact ⟨c, hac, .refl⟩
  · obtain rfl | ⟨a2, ha2, ha2c⟩ := hac.cases_head
    · exact ⟨b, .refl, hab⟩
    · obtain ⟨d, ha1d, ha2d⟩ := hlc a a1 a2 ha1 ha2
      obtain ⟨e, hbe, hde⟩ := ih a1 ha1 b d ha1b ha1d
      obtain ⟨f, hcf, hef⟩ := ih a2 ha2 c e ha2c (ha2d.trans hde)
      exact ⟨f, hbe.trans hef, hcf⟩

/-- Confluence of the runtime's rewrite relation: if a measure strictly decreases on every step and the
    relation is locally confluent, it is confluent. Termination comes from the measure (the step
    relation is well-founded read backwards); confluence then follows by Newman's lemma. -/
theorem rewStep_confluent_of_measure (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t)
    (hlc : LocallyConfluent (RewStep p)) : Confluent (RewStep p) := by
  refine newman (RewStep p) ?_ hlc
  have hsub : Subrelation (fun b a => RewStep p a b) (InvImage (· < ·) μ) :=
    fun {x y} h => hμ y x h
  exact hsub.wf (InvImage.wf μ Nat.lt_wfRel.wf)

/-- A normal form (one with no outgoing step) only reduces to itself. -/
theorem eq_of_reflTransGen_of_normal {r : α → α → Prop} {a b : α}
    (h : ReflTransGen r a b) (hn : ∀ x, ¬ r a x) : a = b := by
  rcases h.cases_head with heq | ⟨c, hac, _⟩
  · exact heq
  · exact absurd hac (hn c)

/-- Under confluence, normal forms are unique: two normal forms reachable from the same term are equal.
    This is why a confluent, terminating runtime has a well-defined answer. -/
theorem unique_normal_form {r : α → α → Prop} (hc : Confluent r) {a n₁ n₂ : α}
    (h₁ : ReflTransGen r a n₁) (h₂ : ReflTransGen r a n₂)
    (hn₁ : ∀ x, ¬ r n₁ x) (hn₂ : ∀ x, ¬ r n₂ x) : n₁ = n₂ := by
  obtain ⟨m, hm₁, hm₂⟩ := hc a n₁ n₂ h₁ h₂
  rw [eq_of_reflTransGen_of_normal hm₁ hn₁, eq_of_reflTransGen_of_normal hm₂ hn₂]

/-- A relation is deterministic when each element has at most one successor. -/
def Deterministic (r : α → α → Prop) : Prop := ∀ a b c, r a b → r a c → b = c

/-- A deterministic relation is locally confluent: the two one-step reducts coincide, so they are
    trivially joinable. This discharges `LocallyConfluent` for deterministic systems directly, without
    critical-pair analysis. The general route, deciding local confluence by computing critical pairs and
    checking they are joinable (Knuth-Bendix-Huet), needs unification of rule left-hand sides and the
    Critical Pair Lemma; that is a separate development (cf. IsaFoR/CeTA) and remains future work. -/
theorem locallyConfluent_of_deterministic {r : α → α → Prop} (h : Deterministic r) :
    LocallyConfluent r := by
  intro a b c hab hac
  have hbc : b = c := h a b c hab hac
  subst hbc
  exact ⟨b, ReflTransGen.refl, ReflTransGen.refl⟩

/-- A deterministic, measure-decreasing rewrite system is confluent: determinism gives local confluence,
    the measure gives termination, and Newman's lemma closes it. -/
theorem rewStep_confluent_of_deterministic_of_measure (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t) (hdet : Deterministic (RewStep p)) :
    Confluent (RewStep p) :=
  rewStep_confluent_of_measure p μ hμ (locallyConfluent_of_deterministic hdet)

end MeTTaIL
