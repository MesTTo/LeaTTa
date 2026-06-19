import MettaHyperonFull.Operational.Trace

namespace Metta

/-- Observable properties of a machine state. An external observer can test whether a given atom is
    present in the input, workspace, or output register. -/
inductive Barb where
  | input : Atom → Barb
  | work : Atom → Barb
  | output : Atom → Barb
  deriving Repr, BEq

namespace Barb

def holds (b : Barb) (s : State) : Bool :=
  match b with
  | Barb.input a => s.input.contains a
  | Barb.work a => s.work.contains a
  | Barb.output a => s.output.contains a

end Barb


/-- A relation `R` is a barbed simulation for `cfg` when: (1) related states agree on every barb,
    and (2) every step of the left state is matched by a step of the right state that stays in `R`. -/
def IsBarbedSimulation (cfg : RuntimeConfig) (R : State → State → Prop) : Prop :=
  ∀ s t, R s t →
    (∀ b : Barb, b.holds s = b.holds t) ∧
    (∀ k s', smallStep? cfg s = some (k, s') →
      ∃ k' t', smallStep? cfg t = some (k', t') ∧ R s' t')

/-- A barbed bisimulation is a relation that is a barbed simulation in both directions simultaneously. -/
def IsBarbedBisimulation (cfg : RuntimeConfig) (R : State → State → Prop) : Prop :=
  IsBarbedSimulation cfg R ∧ IsBarbedSimulation cfg (fun s t => R t s)

/-- Barbed bisimilarity (arXiv:2305.17218 §5): `s` and `t` are bisimilar when there exists some
    barbed bisimulation relating them. This is the greatest such relation. -/
def Bisimilar (cfg : RuntimeConfig) (s t : State) : Prop :=
  ∃ R, IsBarbedBisimulation cfg R ∧ R s t

/-- Bisimilarity is reflexive. Proof: equality is itself a barbed bisimulation. -/
theorem Bisimilar.refl (cfg : RuntimeConfig) (s : State) : Bisimilar cfg s s := by
  refine ⟨(· = ·), ⟨?_, ?_⟩, rfl⟩
  all_goals
    rintro p q rfl
    exact ⟨fun _ => rfl, fun k s' hs => ⟨k, s', hs, rfl⟩⟩

/-- Bisimilarity is symmetric. Proof: reading a bisimulation backwards still satisfies the
    definition. -/
theorem Bisimilar.symm (cfg : RuntimeConfig) {s t : State} :
    Bisimilar cfg s t → Bisimilar cfg t s := by
  rintro ⟨R, ⟨hf, hb⟩, hst⟩
  exact ⟨fun a b => R b a, ⟨hb, hf⟩, hst⟩

/-- Bisimilarity is transitive. Proof: the relational composition of two barbed bisimulations is
    itself a barbed bisimulation. -/
theorem Bisimilar.trans (cfg : RuntimeConfig) {s t u : State} :
    Bisimilar cfg s t → Bisimilar cfg t u → Bisimilar cfg s u := by
  rintro ⟨R₁, ⟨hf₁, hb₁⟩, h₁⟩ ⟨R₂, ⟨hf₂, hb₂⟩, h₂⟩
  refine ⟨fun a c => ∃ b, R₁ a b ∧ R₂ b c, ⟨?_, ?_⟩, t, h₁, h₂⟩
  · rintro a c ⟨b, hab, hbc⟩
    refine ⟨fun bar => ((hf₁ a b hab).1 bar).trans ((hf₂ b c hbc).1 bar), ?_⟩
    intro k a' ha'
    obtain ⟨k₁, b', hb', hab'⟩ := (hf₁ a b hab).2 k a' ha'
    obtain ⟨k₂, c', hc', hbc'⟩ := (hf₂ b c hbc).2 k₁ b' hb'
    exact ⟨k₂, c', hc', b', hab', hbc'⟩
  · rintro x y ⟨b, hyb, hbx⟩
    refine ⟨fun bar => (((hf₁ y b hyb).1 bar).trans ((hf₂ b x hbx).1 bar)).symm, ?_⟩
    intro k x' hx'
    obtain ⟨k₂, b', hb', hbx'⟩ := (hb₂ x b hbx).2 k x' hx'
    obtain ⟨k₁, y', hy', hyb'⟩ := (hb₁ b y hyb).2 k₂ b' hb'
    exact ⟨k₁, y', hy', b', hyb', hbx'⟩

/-- Check whether two states produce the same output register after `fuel` steps.

    This is a cheap necessary condition for bisimilarity (bisimilar states agree on output barbs).
    It is not a decision procedure for `Bisimilar`: it ignores the step-matching requirement and the
    input/workspace barbs. A positive result does not imply bisimilarity. Use it as a fast falsifier
    only. -/
def outputAgreesAfter (cfg : RuntimeConfig) (fuel : Nat) (s t : State) : Bool :=
  (runFuel cfg fuel s).output == (runFuel cfg fuel t).output

end Metta
