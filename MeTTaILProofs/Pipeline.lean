-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MeTTaILProofs.Pipeline
Layer: Proofs
Purpose: Invariants of the elaboration and transformation pipeline. These structural guarantees hold
  regardless of the input. The three transformation passes (desugar, type-lift, monomorphize) touch
  only the term list, so they preserve the exports, equations, rewrites, and references, and they
  only extend the terms because the originals remain in order as a prefix. Elaborating the empty
  instance gives the empty presentation. These are the equality-free half of the Layer-1/2
  metatheory; the lattice laws live separately because they need decidable equality.
Imports: MeTTaIL.Theory.Elaborate, MeTTaIL.Transform.Desugar, MeTTaIL.Transform.TypeLift,
  MeTTaIL.Transform.Monomorphize
Trusted boundary: none (fully proved)
Main exports: elaborate_empty; the component-preservation simp lemmas desugarBinds_*, typeLift_*,
  monomorphize_*; the prefix-extension results typeLift_terms_extends, monomorphize_terms_extends,
  desugarBinds_terms.
Open obligations: none
-/
import MeTTaIL.Theory.Elaborate
import MeTTaIL.Transform.Desugar
import MeTTaIL.Transform.TypeLift
import MeTTaIL.Transform.Monomorphize

namespace MeTTaIL

/-- Elaborating the empty theory instance yields the empty presentation. -/
theorem elaborate_empty (ctx : ElabCtx) : elaborate ctx .empty = .ok .empty := rfl

/-! ### DesugarBinds preserves everything but the terms -/

@[simp] theorem desugarBinds_exports (p : Presentation) :
    (desugarBinds p).exports = p.exports := rfl
@[simp] theorem desugarBinds_equations (p : Presentation) :
    (desugarBinds p).equations = p.equations := rfl
@[simp] theorem desugarBinds_rewrites (p : Presentation) :
    (desugarBinds p).rewrites = p.rewrites := rfl
@[simp] theorem desugarBinds_references (p : Presentation) :
    (desugarBinds p).references = p.references := rfl

/-! ### The type-lift preserves everything but the terms -/

@[simp] theorem typeLift_exports (p : Presentation) :
    (typeLift p).exports = p.exports := rfl
@[simp] theorem typeLift_equations (p : Presentation) :
    (typeLift p).equations = p.equations := rfl
@[simp] theorem typeLift_rewrites (p : Presentation) :
    (typeLift p).rewrites = p.rewrites := rfl
@[simp] theorem typeLift_references (p : Presentation) :
    (typeLift p).references = p.references := rfl

/-! ### Monomorphization preserves everything but the terms -/

@[simp] theorem monomorphize_exports (p : Presentation) :
    (monomorphize p).exports = p.exports := rfl
@[simp] theorem monomorphize_equations (p : Presentation) :
    (monomorphize p).equations = p.equations := rfl
@[simp] theorem monomorphize_rewrites (p : Presentation) :
    (monomorphize p).rewrites = p.rewrites := rfl
@[simp] theorem monomorphize_references (p : Presentation) :
    (monomorphize p).references = p.references := rfl

/-! ### The passes only extend the term list -/

/-- The type-lift keeps the original symbols (as a prefix) and only appends companions. -/
theorem typeLift_terms_extends (p : Presentation) :
    ∃ ts, (typeLift p).terms = p.terms ++ ts := ⟨_, rfl⟩

/-- Monomorphization keeps the (monomorphized) original symbols as a prefix and appends the generated
    constructor rules. -/
theorem monomorphize_terms_extends (p : Presentation) :
    ∃ ts, (monomorphize p).terms = p.terms.map Rule.mono ++ ts := ⟨_, rfl⟩

/-- Desugaring is term-local: every original rule still appears, in order, possibly with a
    `...ToArrow` companion inserted after it. -/
theorem desugarBinds_terms (p : Presentation) :
    (desugarBinds p).terms = p.terms.flatMap (fun r => if r.hasBind then [r, r.toArrow] else [r]) :=
  rfl

end MeTTaIL
