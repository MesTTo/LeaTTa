-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational.Properties
Layer: Operational
Purpose: Verified properties of the four-register machine and its resource-bounded extension, as
  published in Meta-MeTTa (arXiv 2305.17218). Three results carry the weight. `mem_equalityReductions`
  characterises the QUERY result set as sound and complete: a reduct appears iff it is a genuine
  instantiated equality-rule firing. `smallStep?_kb_auditable` shows a single step changes the
  knowledge base only by an explicit `add-atom`/`remove-atom`, so every change to contract state is
  attributable. `resourceStep?_energy_nonincreasing` shows a resource-bounded step never creates
  energy, so total gas is monotonically non-increasing. These extend the bisimulation results.
Imports: MettaHyperonFull.Operational.ResourceBounded
Trusted boundary: none (fully proved)
Main exports: mem_equalityReductions, equalityStep_eq_none_iff, firedReducts, mem_firedReducts,
  smallStep?_kb_auditable, transitionCost_nonneg, debit_energy_le,
  resourceStep?_energy_nonincreasing
Open obligations: none
-/
import MettaHyperonFull.Operational.ResourceBounded

namespace Metta

/-! ## QUERY result set: sound and complete -/

/-- The `[]` arm of the inner `match` in `equalityReductions` agrees with `[].map`, so the whole
    expression collapses to a `flatMap`. -/
theorem equalityReductions_eq (s : Space) (a : Atom) :
    equalityReductions s a =
      s.equalityRules.flatMap fun p => (matchAtoms p.fst a).map fun b => instantiate b p.snd := by
  unfold equalityReductions
  congr 1
  funext p
  cases matchAtoms p.fst a <;> rfl

/-- The reducts obtained by firing a list of equality rules at `a`: for each rule `(l, r)` and each
    unifier `b` of `l` against `a`, the result is `instantiate b r`. This is the shared kernel of
    both QUERY semantics. MOPS fires it over the whole knowledge base; the indexed kernel
    (`Proofs/Correspondence.lean`) fires it over the first-argument-indexed candidates only. -/
def firedReducts (rules : List (Atom × Atom)) (a : Atom) : List Atom :=
  rules.flatMap fun p => (matchAtoms p.fst a).map fun b => instantiate b p.snd

/-- `x ∈ firedReducts rules a` iff some rule `(l, r) ∈ rules` has a unifier `b` of `l` against `a`
    with `x = instantiate b r`. Used by both QUERY soundness-and-completeness proofs. -/
theorem mem_firedReducts {x a : Atom} {rules : List (Atom × Atom)} :
    x ∈ firedReducts rules a ↔ ∃ p ∈ rules, ∃ b ∈ matchAtoms p.fst a, x = instantiate b p.snd := by
  unfold firedReducts
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [List.mem_map] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    exact ⟨p, hp, b, hb, hxb.symm⟩
  · rintro ⟨p, hp, b, hb, hxb⟩
    exact ⟨p, hp, List.mem_map.2 ⟨b, hb, hxb.symm⟩⟩

theorem equalityReductions_eq_fired (s : Space) (a : Atom) :
    equalityReductions s a = firedReducts s.equalityRules a :=
  equalityReductions_eq s a

/-- QUERY soundness and completeness. `x ∈ equalityReductions s a` iff there is a rule
    `(l, r) ∈ s.equalityRules` and a unifier `b` of `l` against `a` with `x = instantiate b r`.
    Nothing is invented and nothing is dropped. -/
theorem mem_equalityReductions {x a : Atom} {s : Space} :
    x ∈ equalityReductions s a ↔
      ∃ p ∈ s.equalityRules, ∃ b ∈ matchAtoms p.fst a, x = instantiate b p.snd := by
  rw [equalityReductions_eq_fired]; exact mem_firedReducts

/-- `equalityStep s a = none` iff no equation in `s` reduces `a`. This is the executable form of
    MOPS's `insensitive` predicate (arXiv:2305.17218 §3.3). -/
theorem equalityStep_eq_none_iff {s : Space} {a : Atom} :
    equalityStep s a = none ↔ equalityReductions s a = [] := by
  unfold equalityStep
  cases h : equalityReductions s a <;> simp

/-! ## Knowledge-base auditability (on-chain state integrity) -/

/-- `foldl State.pushWork` only modifies the workspace, not the knowledge base. -/
theorem foldl_pushWork_kb (reds : List Atom) (s : State) :
    (reds.foldl State.pushWork s).kb = s.kb := by
  induction reds generalizing s with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, ih]; rfl

/-! ## Input consumption for command atoms -/

/-- `stepAddAtom` consumes exactly the command atom it was passed. -/
theorem stepAddAtom_input_eq (s : State) (call a : Atom) :
    (stepAddAtom s call a).input = Space.removeOne s.input call :=
  rfl

/-- `stepRemAtom` consumes exactly the command atom it was passed. -/
theorem stepRemAtom_input_eq (s : State) (call a : Atom) :
    (stepRemAtom s call a).input = Space.removeOne s.input call :=
  rfl

/-- The dashed add spelling dispatches to `stepAddAtom` with the same dashed command atom. -/
theorem smallStep?_addAtomDash_eq_stepAddAtom (cfg : RuntimeConfig) (s : State) (x : Atom)
    (rest : List Atom) :
    smallStep? cfg { s with input := ⟨Atom.expr [Atom.sym "add-atom", x] :: rest⟩ } =
      some (StepKind.addAtom,
        stepAddAtom { s with input := ⟨Atom.expr [Atom.sym "add-atom", x] :: rest⟩ }
          (Atom.expr [Atom.sym "add-atom", x]) x) :=
  rfl

/-- The camel add spelling dispatches to `stepAddAtom` with the same camel command atom. -/
theorem smallStep?_addAtomCamel_eq_stepAddAtom (cfg : RuntimeConfig) (s : State) (x : Atom)
    (rest : List Atom) :
    smallStep? cfg { s with input := ⟨Atom.expr [Atom.sym "addAtom", x] :: rest⟩ } =
      some (StepKind.addAtom,
        stepAddAtom { s with input := ⟨Atom.expr [Atom.sym "addAtom", x] :: rest⟩ }
          (Atom.expr [Atom.sym "addAtom", x]) x) :=
  rfl

/-- The dashed remove spelling dispatches to `stepRemAtom` with the same dashed command atom. -/
theorem smallStep?_remAtomDash_eq_stepRemAtom (cfg : RuntimeConfig) (s : State) (x : Atom)
    (rest : List Atom) :
    smallStep? cfg { s with input := ⟨Atom.expr [Atom.sym "remove-atom", x] :: rest⟩ } =
      some (StepKind.remAtom,
        stepRemAtom { s with input := ⟨Atom.expr [Atom.sym "remove-atom", x] :: rest⟩ }
          (Atom.expr [Atom.sym "remove-atom", x]) x) :=
  rfl

/-- The camel remove spelling dispatches to `stepRemAtom` with the same camel command atom. -/
theorem smallStep?_remAtomCamel_eq_stepRemAtom (cfg : RuntimeConfig) (s : State) (x : Atom)
    (rest : List Atom) :
    smallStep? cfg { s with input := ⟨Atom.expr [Atom.sym "remAtom", x] :: rest⟩ } =
      some (StepKind.remAtom,
        stepRemAtom { s with input := ⟨Atom.expr [Atom.sym "remAtom", x] :: rest⟩ }
          (Atom.expr [Atom.sym "remAtom", x]) x) :=
  rfl

/-- Knowledge-base auditability. One small step either leaves `kb` unchanged (`QUERY`/`CHAIN`/`OUTPUT`)
    or inserts exactly one atom (`add-atom`) or removes exactly one atom (`remove-atom`). No reduction
    step mutates the knowledge base as a side effect. -/
theorem smallStep?_kb_auditable {cfg : RuntimeConfig} {s : State} {k : StepKind} {s' : State}
    (h : smallStep? cfg s = some (k, s')) :
    s'.kb = s.kb ∨ (∃ x, s'.kb = Space.insert s.kb x) ∨ (∃ x, s'.kb = Space.removeOne s.kb x) := by
  unfold smallStep? at h
  split at h
  · -- input register non-empty
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact Or.inr (Or.inl ⟨_, rfl⟩)                                   -- add-atom
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact Or.inr (Or.inl ⟨_, rfl⟩)                                   -- addAtom
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact Or.inr (Or.inr ⟨_, rfl⟩)                                   -- remove-atom
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
      exact Or.inr (Or.inr ⟨_, rfl⟩)                                   -- remAtom
    · split at h                                                       -- general atom: reduce
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
        exact Or.inl (foldl_pushWork_kb _ _)                           -- QUERY
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
        exact Or.inl rfl                                               -- OUTPUT (from input)
  · -- input empty: drain the workspace
    split at h
    · simp at h                                                        -- workspace empty → no step
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
        exact Or.inl (foldl_pushWork_kb _ _)                           -- CHAIN
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
        exact Or.inl rfl                                               -- OUTPUT (from workspace)

/-! ## Gas: energy is never created (resource-bounded extension) -/

def totalEnergy (toks : List ResourceToken) : Int :=
  toks.foldr (fun t acc => t.energy + acc) 0

/-- `transitionCost` is always non-negative (it is `Atom.size` cast to `Int`). -/
theorem transitionCost_nonneg (a : Atom) : 0 ≤ transitionCost a := by
  unfold transitionCost; exact Int.natCast_nonneg _

/-- After debiting token `t` by the cost of `a`, the remaining energy is at most what `t` started
    with. -/
theorem debit_energy_le (t : ResourceToken) (a : Atom) : (debit t a).energy ≤ t.energy := by
  have hnn := transitionCost_nonneg a
  have he : (debit t a).energy = t.energy - transitionCost a := rfl
  rw [he]; omega

/-- Gas is never created. A resource-bounded step debits the head token by the transition cost and
    leaves the rest of the token list untouched, so total energy is monotonically non-increasing. -/
theorem resourceStep?_energy_nonincreasing {cfg : RuntimeConfig} {rs rs' : ResourceState}
    (h : resourceStep? cfg rs = some rs') :
    totalEnergy rs'.tokens ≤ totalEnergy rs.tokens := by
  unfold resourceStep? at h
  cases hin : rs.state.input.atoms with
  | nil => rw [hin] at h; simp at h                                    -- empty input: no step
  | cons a tail =>
    cases htok : rs.tokens with
    | nil => rw [hin, htok] at h; simp at h                            -- no tokens: no step
    | cons t ts =>
      rw [hin, htok] at h
      simp only at h
      split at h                                                       -- if affordable
      · split at h                                                     -- match smallStep?
        · -- inner step succeeded: rs' = { rs with …, tokens := debit t a :: ts }
          simp only [Option.some.injEq] at h
          have htok' : rs'.tokens = debit t a :: ts := by rw [← h]
          rw [htok']
          simp only [totalEnergy, List.foldr_cons]
          have := debit_energy_le t a
          omega
        · simp at h                                                    -- inner step failed
      · simp at h                                                      -- unaffordable

end Metta
