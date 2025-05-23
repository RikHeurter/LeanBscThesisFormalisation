import Mathlib

-- TODO: change this everywhere.
-- TODO: Cleanup the code capitalisation everywhere you go, always take the weather with you.
local notation "ℝ(" n ")" => (PiLp 1 fun (x : (Fin n)) => ℝ) -- by: https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/.60parameter.60.20in.20Lean.204.3F/near/479123468
local notation "ℕ(" n ")" => (PiLp 1 fun (x : (Fin n)) => ℕ)

def coreSpace (n : ℕ) (c : ℕ(n)) : Set (ℝ(n)) :=
  {x : ℝ(n)  | ∀ {i : Fin n}, x i ≤ c i ∧ ∀ i, x i ≥ 0}

def myConcave (n : ℕ) (c : ℕ(n)) (f : ℝ(n) → ℝ) : Prop :=
  ∀ x, x ∈ (coreSpace n c) → ∀ y, y ∈ (coreSpace n c) → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

def Sublinear (n : ℕ) (speedvec: ℝ(n)) (f : ℝ(n) → ℝ) : Prop :=
  (∀ x, ‖x‖ ≥ 0 → ‖f x‖ ≤ dotProduct speedvec x) ∧ (∃ c > 0, ∀ x, ‖x‖ ≥ 0 → ‖f x‖ ≤ c)

def nonDecreasing (n : ℕ) (f : ℝ(n) → ℝ) : Prop :=
  ∀x, ‖x‖ ≥ 0 → ∀ε, ‖ε‖ > 0 → f x ≤ f (x + ε)

def SpeedUpFunction (n : ℕ ) (speedvec: ℝ(n)) (c : ℕ(n)) (f : ℝ(n) → ℝ) : Prop :=
  Sublinear n speedvec f ∧ myConcave n c f ∧ nonDecreasing n f

structure RateMatrix where
  Q : ℕ → ℕ → ℝ
  sum_eq_zero_at_zero : Q 0 1 = -(Q 0 0)
  sum_eq_zero_at_non_zero : ∀ n, n ≠ 0 → (Q n (n+1)) + (Q n (n-1)) = -(Q n n)
  non_nbr_eq_zero : ∀n, ∀k, k ≥ n + 2 → (Q n k) = 0 ∧ (Q k n) = 0
  arrival_rate_greater_than_zero : ∀ n, 0 ≤ (Q n (n+1))
  departure_rate_greater_than_zero : ∀ n, n ≠ 0 → 0 ≤ (Q (n+1) n)
  -- Q_pos_neg_eq_pos_pos : ∀i, i ≥ 0 → ∀j, j < 0 → Q i j = Q i -j
  -- TODO: Prove this later on.
-- variable (n : ℕ ) (s : Euclidean Space ℝ  (Fin n)) (distributionpolicy: ℕ → ℕ)
--                           (p: ℕ → ℕ → (EuclideanSpace ℝ  (Fin n))) (j : Fin n)
-- #check (∑i ∈ (Finset.range (distributionpolicy n)), (p n i)) j

def Policy (n : ℕ) (c : ℕ(n)) (distributionpolicy: ℕ → ℕ)
                          (p: ℕ → ℕ → (ℝ(n))) : Prop :=
  ∀ n, distributionpolicy n ≤ n
    ∧ distributionpolicy n ≥ 0
    ∧ (∀j, (∑i : (Fin (distributionpolicy n)), (p n i)) j ≤ c j)
    ∧ (∀j, ∀ i, (p n i) j ≥ 0)

structure SchedulePolicy where
  dim : ℕ
  μ : ℝ
  cN : ℕ(dim)
  cR : ℝ(dim)
  speedvector : ℝ(dim)
  speedupF : (ℝ(dim)) → ℝ
  distributionpolicy: ℕ → ℕ
  policy: ℕ → ℕ → (ℝ(dim))
  departurerates : ℕ → ℝ
  speedupF_is_speedup : SpeedUpFunction dim speedvector cN speedupF
  ispolicy : Policy dim cN distributionpolicy policy
  departurerates_uses_speedup: ∀ n, μ * ∑i : (Fin (distributionpolicy n)), speedupF (policy n i) = (departurerates n)
  cR_eq_cN : ∀ i, cN i = cR i
  -- departurerates_contant_after_n: ∀n : ℕ, n ≥ ⌈‖cR‖⌉₊ → departurerates n = departurerates ⌈‖cR‖⌉₊
  -- TODO: require that after n becomes greater than ||c||_1 that it actually is indeed the same constantly.
  -- Otherwise is stable is way more difficult to implement.

-- #check Function.comp
-- #check Norm.norm.

def IsStable (P : SchedulePolicy) (Λ : ℝ) : Prop :=
  ∃c : ℝ, c > 0 → ∃N : ℕ, ∀ n : ℕ, n ≥ N → (P.departurerates n)/Λ ≤ (1 - c)

def ConstantArrival (Q : RateMatrix) (Λ : ℝ) : Prop :=
  ∀ i, Q.Q i (i + 1) = Λ
  -- (P.departurerates ⌈‖P.cR‖⌉₊)/Λ < 1
  -- (⨆ (z : ℕ), P.departurerates z)/Λ < 1

structure queue where
  state_space : ℕ
  Λ : ℝ
  μ : ℝ
  Q : RateMatrix
  P : SchedulePolicy
  policy_mu_eq_queue_mu : P.μ = μ
  stable_policy : IsStable P Λ
  isConstant : ConstantArrival Q Λ

-- #check ∑'

-- def SumSeq (n : ℕ) (lambda : ℕ → ℝ) : ℝ :=
--   ∑ i∈ (Finset.range n), (lambda (i+1))

-- def AllPositive (lambda : ℕ → ℝ) : Prop :=
--   ∀ n, 0 ≤ lambda n

-- https://leanprover-community.github.io/mathlib_docs/algebra/geom_sum.html
-- def NormalizedVec (lambda : ℕ → ℝ) : Prop :=
--   ∀ ε > 0, ∃ N, ∀ n ≥ N, |(SumSeq n lambda) - 1| < ε

def InvariantDistribution (Que : RateMatrix) (lambda : ℕ → ℝ) : Prop :=
  (∀ n, n ≠ 0 → (lambda (n-1)) * (Que.Q (n-1) n) + (lambda (n+1)) * (Que.Q (n+1) n) = (Que.Q n (n+1) + Que.Q n (n-1)) * lambda n)
  ∧ ((lambda 1) * (Que.Q 1 0) = (Que.Q 0 1) * lambda 0)
  ∧ ∑' i, lambda i = 1

noncomputable
def MeanNumberInSystem (Que : RateMatrix) (lambda : ℕ → ℝ) (_ : InvariantDistribution Que lambda): ℝ :=
  ∑' i, i * (lambda i)

noncomputable
def MeanResponseTime (lambda : ℕ → ℝ) (Q : queue) (_ : InvariantDistribution Q.Q lambda) : ℝ :=
    (∑' i, lambda i * i)/Q.Λ
-- #check Σ'


-- Definition of Mean Response Time using Little's law, because I didn't want
-- to go into the actual case-specific definition.
-- noncomputable
-- def MRTSequence (n : ℕ) (Que : queue) (lambda : ℕ → ℝ) (_ : InvariantDistribution Que lambda) : ℝ :=
--   (∑ i ∈ (Finset.range n), lambda i)/Que.Λ

-- noncomputable
-- def isMRT (Que : queue) (lambda : ℕ → ℝ) (h : InvariantDistribution Que lambda) (L : ℝ) : Prop :=
--   ∀ε > 0, ∃ N, ∀ n ≥ N, |(MRTSequence n Que lambda h) - L| < ε


structure MeanResponseTimePolicy where
  L : ℝ
  lambda : ℕ → ℝ
  Q : queue
  isID : InvariantDistribution Q.Q lambda
  isMRT : MeanResponseTime lambda Q isID = L
