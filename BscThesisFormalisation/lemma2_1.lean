import Mathlib
import BscThesisFormalisation.definitions

local notation "ℝ(" n ")" => (PiLp 1 fun (x : (Fin n)) => ℝ) -- by: https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.60parameter.60.20in.20Lean.204.3F/near/479123468
local notation "ℕ(" n ")" => (PiLp 1 fun (x : (Fin n)) => ℕ)

theorem lemma2_1 (n : ℕ) (speedvec : ℝ(n)) (cN : ℕ(n)) (cR : ℝ(n)) (s : ℝ(n) → ℝ)
  (h : SpeedUpFunction n speedvec cN s) (h₂ : ∀ i, cN i = cR i): ∀ i, i ≠ 0 → i < ‖cR‖ → ∃ε > 0, i * s ((1/i)•cR) < (i+ε) * s ((1/(i+ε))•cR)
  ∧ ∀ i, i ≠ 0 → i ≥ ‖cR‖ → ∀ε > 0, i * s ((1/i)•cR) ≤ (i+ε) * s ((1/(i+ε))•cR) := by
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
