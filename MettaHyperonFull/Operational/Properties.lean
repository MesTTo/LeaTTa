import MettaHyperonFull.Operational.ResourceBounded

/-!
# Properties of the Meta-MeTTa operational semantics

Verified properties of the four-register machine (`Operational/Semantics.lean`) and its
resource-bounded extension (`Operational/ResourceBounded.lean`): the operational model published in
*Meta-MeTTa* (arXiv 2305.17218). These complement the barbed-bisimulation equivalence already proved
in `Operational/Bisimulation.lean`; together they make the small-step machine a *verified* spec, not
just an executable sketch.

The two headline results are exactly the guarantees MeTTa needs for its intended **on-chain /
smart-contract** use:

* **`smallStep?_kb_auditable`**: a single step changes the knowledge base *only* by an explicit
  `add-atom`/`remove-atom`; pure reduction (`QUERY`/`CHAIN`/`OUTPUT`) never mutates it. So every change
  to contract state is an attributable, authorised operation.
* **`resourceStep?_energy_nonincreasing`**: a resource-bounded step never *creates* energy; total
  gas is monotonically non-increasing. (With `transitionCost ≥ 0`, every transition is paid for.)

Plus `mem_equalityReductions`, the soundness-and-completeness characterisation of `QUERY`'s result
set: a reduct is produced *iff* it is a genuine instantiated equation firing.
-/

namespace Metta

/-! ## QUERY result set: sound and complete -/

/-- The inner `match` in `equalityReductions` is just `List.map` (the `[]` arm agrees with
`[].map`). -/
theorem equalityReductions_eq (s : Space) (a : Atom) :
    equalityReductions s a =
      s.equalityRules.flatMap fun p => (matchAtoms p.fst a).map fun b => instantiate b p.snd := by
  unfold equalityReductions
  congr 1
  funext p
  cases matchAtoms p.fst a <;> rfl

/-- The reducts obtained by firing a list of equality rules `(l, r)` at the redex `a`: for each rule
and each unifier `b` of its LHS `l` with `a`, the instantiated RHS `instantiate b r`. This is the
shared kernel of both QUERY semantics. MOPS (here) fires it over the whole knowledge base; the
kernel fires it over the first-argument-indexed candidates (`Proofs/Correspondence.lean`). -/
def firedReducts (rules : List (Atom × Atom)) (a : Atom) : List Atom :=
  rules.flatMap fun p => (matchAtoms p.fst a).map fun b => instantiate b p.snd

/-- Membership in `firedReducts`: `x` is fired iff some rule's LHS unifies with `a` (binding `b`) and
`x` is the instantiated RHS. The sound-and-complete characterisation reused by both QUERY semantics. -/
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

/-- The operational `equalityReductions` is exactly `firedReducts` over the space's equality rules. -/
theorem equalityReductions_eq_fired (s : Space) (a : Atom) :
    equalityReductions s a = firedReducts s.equalityRules a :=
  equalityReductions_eq s a

/-- **QUERY is sound and complete.** An atom `x` is an equality-rule reduct of `a` in space `s`
*iff* it is `instantiate b r` for a genuine rule `(= l r) ∈ s` (`(l, r) ∈ s.equalityRules`) and a
matcher binding `b` of the rule's LHS against `a`. The workspace receives exactly the genuine
instantiated rule firings: nothing invented, nothing dropped. -/
theorem mem_equalityReductions {x a : Atom} {s : Space} :
    x ∈ equalityReductions s a ↔
      ∃ p ∈ s.equalityRules, ∃ b ∈ matchAtoms p.fst a, x = instantiate b p.snd := by
  rw [equalityReductions_eq_fired]; exact mem_firedReducts

/-- **Irreducibility is decidable as "no rule fires".** `a` is a normal form (`equalityStep` yields
`none`) iff no equation in `s` reduces it, which is MOPS's `insensitive` predicate, made executable. -/
theorem equalityStep_eq_none_iff {s : Space} {a : Atom} :
    equalityStep s a = none ↔ equalityReductions s a = [] := by
  unfold equalityStep
  cases h : equalityReductions s a <;> simp

/-! ## Knowledge-base auditability (on-chain state integrity) -/

/-- Draining results into the workspace never touches the knowledge base. -/
theorem foldl_pushWork_kb (reds : List Atom) (s : State) :
    (reds.foldl State.pushWork s).kb = s.kb := by
  induction reds generalizing s with
  | nil => rfl
  | cons r rs ih => rw [List.foldl_cons, ih]; rfl

/-- **On-chain state integrity.** One small step changes the knowledge base `kb` only by an explicit
`add-atom` (one atom inserted) or `remove-atom` (one atom removed); `QUERY`/`CHAIN`/`OUTPUT` leave it
untouched. So in the four-register machine the contract's persistent state is mutated *only* by
attributable atom operations, never as a silent side effect of reduction. -/
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

/-- Total energy held across a token list. -/
def totalEnergy (toks : List ResourceToken) : Int :=
  toks.foldr (fun t acc => t.energy + acc) 0

/-- Every transition has non-negative syntactic cost. -/
theorem transitionCost_nonneg (a : Atom) : 0 ≤ transitionCost a := by
  unfold transitionCost; exact Int.natCast_nonneg _

/-- Debiting a token never increases its energy. -/
theorem debit_energy_le (t : ResourceToken) (a : Atom) : (debit t a).energy ≤ t.energy := by
  have hnn := transitionCost_nonneg a
  have he : (debit t a).energy = t.energy - transitionCost a := rfl
  rw [he]; omega

/-- **Gas is never created.** A resource-bounded step debits exactly the head token by the (non-
negative) transition cost and leaves the rest untouched, so the total energy is monotonically
non-increasing: a contract can only ever *spend* gas, never mint it. -/
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
