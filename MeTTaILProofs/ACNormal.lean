-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.ACNormal
Layer: Proofs
Purpose: Normalization modulo AC, and its coherence. The Maude strategy for rewriting modulo a set of
  structural axioms is to work on canonical representatives: canonicalize, rewrite, recanonicalize. Here
  `acNF` canonicalizes a term and normalizes the canonical form with the measure-bounded engine. The
  central result is `acNF_respects`: AC-equivalent terms have the *identical* normal form, not merely an
  AC-equal one. This is the coherence of rewriting modulo AC obtained from the canonical form (the
  abstract framework is Jouannaud and Kirchner's rewriting modulo E): canonicalization collapses each
  AC-equivalence class to a single term, so the deterministic engine that follows is a well-defined
  function on classes. With `acNF_sound` (the normal form is an AC-then-rewrite reduct of the input),
  `acNF_isNormal` (it is a base normal form under a decreasing measure), and `acNF_unique` (under
  confluence it is the unique reachable normal form), this is the Church-Rosser-modulo-AC behaviour of the
  runtime: editing a term within its AC class does not change the computed answer.
Imports: MeTTaILProofs.AC (canon and its soundness/completeness), MeTTaIL.Semantics.Terminate (the
  measure-bounded normalizer), MeTTaILProofs.Newman (confluence, unique normal forms)
Trusted boundary: none (fully proved)
Main exports: acNF, acNF_respects, acNF_isNormal, acNF_sound, acNF_unique
Open obligations: deriving the no-step normality hypothesis of `acNF_unique` from `IsNormal` needs the
  base engine's completeness in the presence of premised rules (the conditional-rewrite gap inherited
  from `Semantics/Normal`); for base presentations it holds.
-/
import MeTTaILProofs.AC
import MeTTaIL.Semantics.Terminate
import MeTTaILProofs.Newman

namespace MeTTaIL.AC

/-- The AC normal form: canonicalize, then normalize the canonical form with the measure-bounded engine.
    Rewriting modulo AC, computed on canonical representatives. -/
def acNF (p : Presentation) (acOp : Label → Bool) (μ : AST → Nat) (t : AST) : AST :=
  eval p (μ (canon acOp t)) (canon acOp t)

/-- Coherence: the AC normalizer is constant on AC-equivalence classes. AC-equivalent terms have the
    identical normal form, because `canon` collapses the class to one term (`canon_complete`) and the
    engine then proceeds deterministically. The runtime is a well-defined function on AC-classes. -/
theorem acNF_respects (acOp : Label → Bool) (p : Presentation) (μ : AST → Nat) {t t' : AST}
    (h : ACEq acOp t t') : acNF p acOp μ t = acNF p acOp μ t' := by
  unfold acNF; rw [canon_complete acOp h]

/-- The AC normal form is a base normal form: no further base rewrite applies, under a decreasing
    measure. -/
theorem acNF_isNormal (acOp : Label → Bool) (p : Presentation) (μ : AST → Nat)
    (hμ : ∀ t t', RewStep p t t' → μ t' < μ t) (t : AST) : IsNormal p (acNF p acOp μ t) :=
  eval_normal_of_measure p μ hμ (canon acOp t)

/-- Soundness: `t` is AC-equivalent to its canonical form, which base-rewrites to the AC normal form. So
    `acNF t` is reached from `t` by AC-equivalence followed by the presentation's own rewrites. -/
theorem acNF_sound (acOp : Label → Bool) (p : Presentation) (μ : AST → Nat) (t : AST) :
    ACEq acOp t (canon acOp t) ∧ RewStepMany p (canon acOp t) (acNF p acOp μ t) :=
  ⟨(canon_sound acOp t).symm, eval_sound p _ (canon acOp t)⟩

/-- The runtime's many-step relation is the reflexive-transitive closure used by the confluence layer.
    `RewStepMany` and `Relation.ReflTransGen (RewStep p)` are the same closure; this is the bridge. -/
theorem rewStepMany_to_reflTransGen {p : Presentation} {t t' : AST} (h : RewStepMany p t t') :
    Relation.ReflTransGen (RewStep p) t t' := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail s

/-- Under confluence of the base engine, the AC normal form is the unique normal form reachable from the
    canonical representative: any base normal form reached from `canon t` equals `acNF t`. Together with
    `acNF_respects`, AC-equivalent terms reduce to one and the same normal form, the Church-Rosser-modulo-
    AC property. The no-step normality hypotheses are exactly "is a normal form"; for base presentations
    they follow from `IsNormal` via the engine's completeness. -/
theorem acNF_unique (acOp : Label → Bool) (p : Presentation) (μ : AST → Nat)
    (hconf : Confluent (RewStep p)) {t n : AST}
    (hreach : RewStepMany p (canon acOp t) n) (hn : ∀ x, ¬ RewStep p n x)
    (hacNF : ∀ x, ¬ RewStep p (acNF p acOp μ t) x) : n = acNF p acOp μ t :=
  unique_normal_form hconf (rewStepMany_to_reflTransGen hreach)
    (rewStepMany_to_reflTransGen (acNF_sound acOp p μ t).2) hn hacNF

end MeTTaIL.AC
