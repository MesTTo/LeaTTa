/-
The mq-calculus of Stay and Meredith ("The MQ-Calculus: A Calculus for Quantum Processes Involving
Intermittent Measurement"), whose driving idea is "communication = measurement": when a quantum state
is sent on a channel and received, it is measured in the computational basis, and the receiver's
continuations are weighted by the Born rule.

We formalize the semantic core that makes that COMM rule well-defined: a finite quantum state is a
normalized vector of complex amplitudes, the Born probability of an outcome is the squared modulus of
its amplitude, and these probabilities form a genuine probability distribution (they are in [0,1] and
sum to one). So measurement-by-communication neither creates nor destroys probability. We also record
interference: Born probabilities of a superposition are not the classical sum, which is exactly why a
received superposition differs from a received mixture.

Mathlib-backed (`Complex`, `Finset.sum`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace MeTTaIL.MQ

open scoped BigOperators

/-- A finite quantum state: complex amplitudes over an `n`-element computational basis, normalized so
    that the squared moduli sum to one (the Born normalization). In the mq-calculus this is the qubit
    register communicated on a channel; receiving it is a measurement. -/
structure QState (n : ℕ) where
  amp : Fin n → ℂ
  normalized : ∑ i, Complex.normSq (amp i) = 1

namespace QState

variable {n : ℕ} (s : QState n)

/-- The Born-rule probability of measuring basis outcome `i`: the squared modulus of its amplitude.
    The mq-calculus COMM rule weights the continuation for outcome `i` by this number. -/
def bornProb (i : Fin n) : ℝ := Complex.normSq (s.amp i)

/-- Every Born probability is nonnegative. -/
theorem bornProb_nonneg (i : Fin n) : 0 ≤ s.bornProb i := Complex.normSq_nonneg _

/-- Probability conservation: the Born probabilities of all outcomes sum to one. So measurement-by-
    communication yields a genuine probability distribution over continuations; the mq-calculus COMM
    rule neither creates nor destroys probability. -/
theorem bornProb_sum : ∑ i, s.bornProb i = 1 := s.normalized

/-- Every Born probability is at most one. -/
theorem bornProb_le_one (i : Fin n) : s.bornProb i ≤ 1 := by
  have h := Finset.single_le_sum (f := s.bornProb)
    (fun j _ => s.bornProb_nonneg j) (Finset.mem_univ i)
  rwa [s.bornProb_sum] at h

end QState

/-- Quantum interference: the Born probability of a superposition is not the sum of the Born
    probabilities of its parts (squared moduli do not add). This is why receiving an interfered state
    differs from receiving a classical mixture of the parts. -/
theorem interference :
    ∃ a b : ℂ, Complex.normSq (a + b) ≠ Complex.normSq a + Complex.normSq b := by
  refine ⟨1, 1, ?_⟩
  simp [Complex.normSq_apply]

end MeTTaIL.MQ
