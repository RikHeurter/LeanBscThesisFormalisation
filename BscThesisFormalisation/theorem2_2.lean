import Mathlib

def isEqui (Que : queue) : Prop :=
  sorry
-- structure EQUIMRT where
--   MRTP : MeanResponseTimePolicy
--   EQUI : sorry

theorem EQUIOptimal (Que : queue) (Equi : MeanResponseTimePolicy) : ∀ x : MeanResponseTimePolicy, isEqui Equi.Q → Equi.L ≤ x.L := by
  sorry
