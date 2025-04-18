import Mathlib


def coreSpace (n : ℕ) (s : (EuclideanSpace ℝ  (Fin n))) : Set (EuclideanSpace ℝ  (Fin n)) :=
  {x : (EuclideanSpace ℝ  (Fin n)) | ‖x‖ ≤ ‖s‖ ∧ ∀ i, x i ≥ 0}

def myConcave (n : ℕ) (s : EuclideanSpace ℝ  (Fin n)) (f : (EuclideanSpace ℝ  (Fin n)) → ℝ) : Prop :=
  ∀ x, x ∈ (coreSpace n s) → ∀ y, y ∈ (coreSpace n s) → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

def Sublinear (n : ℕ) (f : (EuclideanSpace ℝ  (Fin n)) → ℝ) : Prop :=
  ∀ x, ‖x‖ ≥ 0 → ‖f x‖ ≤ ‖x‖

def SpeedUpFunction (n : ℕ ) (s : EuclideanSpace ℝ  (Fin n)) (f : (EuclideanSpace ℝ  (Fin n)) → ℝ) : Prop :=
  Sublinear n f ∧ myConcave n s f

structure RateMatrix where
  Q : ℕ → ℕ → ℝ
  sum_eq_zero_at_zero : Q 0 1 = -(Q 0 0)
  sum_eq_zero_at_non_zero : ∀ n, n ≠ 0 → (Q n (n+1)) + (Q n (n-1)) = -(Q n n)
  non_nbr_eq_zero : ∀n, ∀k, k ≥ n + 2 → (Q n k) = 0 ∧ (Q k n) = 0
-- variable (n : ℕ ) (s : Euclidean Space ℝ  (Fin n)) (distributionpolicy: ℕ → ℕ)
--                           (p: ℕ → ℕ → (EuclideanSpace ℝ  (Fin n))) (j : Fin n)
-- #check (∑i ∈ (Finset.range (distributionpolicy n)), (p n i)) j

def Policy (n : ℕ ) (s : EuclideanSpace ℝ  (Fin n)) (distributionpolicy: ℕ → ℕ)
                          (p: ℕ → ℕ → (EuclideanSpace ℝ  (Fin n))) : Prop :=
  ∀ n, distributionpolicy n ≤ n
    ∧ distributionpolicy n ≥ 0
    ∧ (∀j, (∑i ∈ (Finset.range (distributionpolicy n)), (p n i)) j ≤ s j)
    ∧ (∀j, ∀ i, (p n i) j ≥ 0)

structure SchedulePolicy where
  dim : ℕ
  μ : ℝ
  -- s : Set (EuclideanSpace ℝ  (Fin dim))
  s : EuclideanSpace ℝ  (Fin dim)
  speedupF : (EuclideanSpace ℝ  (Fin dim)) → ℝ
  distributionpolicy: ℕ → ℕ
  policy: ℕ → ℕ → (EuclideanSpace ℝ (Fin dim))
  departurerates : ℕ → ℝ
  speedupF_is_speedup : SpeedUpFunction dim s speedupF
  ispolicy : Policy dim s distributionpolicy policy
  departurerates_uses_speedup: ∀ n, μ * ∑i ∈ (Finset.range (distributionpolicy n)), speedupF (policy n i) = (departurerates n)


def IsStable (P : SchedulePolicy) (Λ : ℝ) : Prop :=
  (⨆ (z : ℕ), P.departurerates z)/Λ < 1

structure queue where
  state_space : ℕ
  Λ : ℝ
  μ : ℝ
  Q : RateMatrix
  P : SchedulePolicy
  policy_mu_eq_queue_mu : P.μ = μ
  stable_policy : IsStable P Λ

def SumSeq (n : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ i∈ (Finset.range n), (lambda (i+1))

def AllPositive (lambda : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ lambda n

-- https://leanprover-community.github.io/mathlib_docs/algebra/geom_sum.html
def NormalizedVec (lambda : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |(SumSeq n lambda) - 1| < ε

def InvariantDistribution (Que : queue) (lambda : ℕ → ℝ) : Prop :=
  ∀ n, n ≠ 0 → (lambda (n-1)) * (Que.Q.Q (n-1) n) + (lambda (n+1)) * (Que.Q.Q (n+1) n) = lambda n
  ∧ (lambda 1) * (Que.Q.Q 1 0) = lambda 0
  ∧ NormalizedVec lambda

-- #check Σ'


-- Definition of Mean Response Time using Little's law, because I didn't want
-- to go into the actual case-specific definition.
noncomputable
def MRTSequence (n : ℕ) (Que : queue) (lambda : ℕ → ℝ) (_ : InvariantDistribution Que lambda) : ℝ :=
  (∑ i ∈ (Finset.range n), lambda i)/Que.Λ

noncomputable
def isMRT (Que : queue) (lambda : ℕ → ℝ) (h : InvariantDistribution Que lambda) (L : ℝ) : Prop :=
  ∀ε > 0, ∃ N, ∀ n ≥ N, |(MRTSequence n Que lambda h) - L| < ε


structure MeanResponseTimePolicy where
  L : ℝ
  lambda : ℕ → ℝ
  Q : queue
  isID : InvariantDistribution Q lambda
  MRT : isMRT Q lambda isID L
