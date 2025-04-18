import Mathlib
import BscThesisFormalisation.definitions

-- TODO: add policy arrivalrates to Q


def isEqui (Que : queue) : Prop :=
  sorry
-- structure EQUIMRT where
--   MRTP : MeanResponseTimePolicy
--   EQUI : sorry

theorem EQUIOptimal (Que : queue) (Equi : MeanResponseTimePolicy) : ∀ x : MeanResponseTimePolicy, isEqui Equi.Q → Equi.L ≤ x.L := by
  sorry

-- variable (n : ℕ) (Que : queue) (lambda : ℕ → ℝ) (h : InvariantDistribution Que lambda)
-- #check ((∑ i ∈ (Finset.range n), lambda i)/Que.Λ)
