import Mathlib
import BscThesisFormalisation.definitions

def isEqui (Que : queue) : Prop :=
  ∀i : ℕ, i ≤ ‖Que.P.cR‖ ∧ i ≠ 0 → (Que.P.departurerates i) = Que.P.μ * i * Que.P.speedupF ((1/i) • Que.P.cR)
  ∧ ∀i : ℕ, i > ‖Que.P.cR‖ → (Que.P.departurerates i) = Que.P.μ * ⌊‖Que.P.cR‖⌋₊ * Que.P.speedupF ((1/⌊‖Que.P.cR‖⌋₊) • Que.P.cR)

def SameSpeedUp (Q : SchedulePolicy) (P : SchedulePolicy) (h : P.dim = Q.dim): Prop :=
  ∀i, ∀j, ∀k, i k = j (Fin.cast h k) ∧ P.speedupF i = Q.speedupF j

theorem EQUIOptimal (Que : queue) (Equi : MeanResponseTimePolicy):
  isEqui Equi.Q → ∀ x : MeanResponseTimePolicy, (h : x.Q.P.dim = Que.P.dim) → SameSpeedUp Que.P x.Q.P h → Equi.L ≤ x.L := by

  sorry
