import Mathlib
import BscThesisFormalisation.definitions

theorem lemma2_1 (n : ℕ) (c : EuclideanSpace ℝ  (Fin n)) (s : (EuclideanSpace ℝ  (Fin n)) → ℝ)
        (h : SpeedUpFunction n c s) : ∀ i, i ≠ 0 → i < ‖c‖ → ∃ε > 0, i * s ((1/i)•c) < (i+ε) * s ((1/(i+ε))•c)
        ∧ ∀ i, i ≠ 0 → i ≥ ‖c‖ → ∀ε > 0, i * s ((1/i)•c) ≤ (i+ε) * s ((1/(i+ε))•c) := by
  sorry
-- theorem NonDecreasingSpeedup (n : ℕ) (c : EuclideanSpace ℝ  (Fin n)) (s : (EuclideanSpace ℝ  (Fin n)) → ℝ)
--         (h : SpeedUpFunction n c s) : ∀ i, i ≠ 0 → i ≥ ‖c‖ → ∀ε > 0, i * s ((1/i)•c) ≤ (i+ε) * s ((1/(i+ε))•c) := by
--   sorry

-- theorem lemma2_1 (n : ℕ) (c : EuclideanSpace ℝ  (Fin n)) (s : (EuclideanSpace ℝ  (Fin n)) → ℝ)
--         (h : SpeedUpFunction n c s) : (IncreasingSpeedup n c s h) ∧ (NonDecreasingSpeedup n c s h) := by
--   sorry

-- TODO: add policy arrivalrates to Q


-- def isEqui (Que : queue) : Prop :=
--   sorry
-- structure EQUIMRT where
--   MRTP : MeanResponseTimePolicy
--   EQUI : sorry

-- theorem EQUIOptimal (Que : queue) (Equi : MeanResponseTimePolicy) : ∀ x : MeanResponseTimePolicy, isEqui Equi.Q → Equi.L ≤ x.L := by
--   sorry

-- variable (n : ℕ) (Que : queue) (lambda : ℕ → ℝ) (h : InvariantDistribution Que lambda)
-- #check ((∑ i ∈ (Finset.range n), lambda i)/Que.Λ)
