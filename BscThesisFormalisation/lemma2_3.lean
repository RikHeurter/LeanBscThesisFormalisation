import Mathlib
import BscThesisFormalisation.definitions

example (a b c d: ℝ) (hb: b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) : a/b = c/d → ∃ e, a = e*c ∧ b = e*d := by
  intro h
  use a/c
  constructor
  · rw [div_eq_mul_one_div, mul_assoc, one_div_mul_eq_div, div_self hc]
    ring
  rw [div_eq_mul_one_div, mul_comm, ←mul_assoc, ←div_eq_mul_one_div]
  symm
  apply (div_eq_iff_mul_eq hc).mpr
  rw [mul_comm]
  apply (div_eq_iff_mul_eq hb).mp
  rw [div_eq_mul_one_div, mul_assoc, mul_comm]
  apply (div_eq_iff_mul_eq hd).mp
  ring_nf
  symm
  exact h

theorem lemma2_3 (P : RateMatrix) (Q : RateMatrix) (lambdaP : ℕ → ℝ) (lambdaQ : ℕ → ℝ):
  (h : (∀ i, P.Q i (i+1) = Q.Q i (i+1) ∧ ∀ i ≠ 0, P.Q i (i-1) ≥ Q.Q i (i-1)) ∧
  (InvariantDistribution P lambdaP ∧ InvariantDistribution Q lambdaQ)) →
  MeanNumberInSystem P lambdaP h.right.left ≥ MeanNumberInSystem Q lambdaQ h.right.right := by sorry

-- example (a b c : ℝ ) (h: b ≠ 0) (h₀ : a ≠ 0) (h₁ : c ≠ 0): a * b = c ↔ a = c/b := by
--   constructor
--   · intro h'
--     rw [eq_div_of_mul_eq h h']
--   intro h'
--   exact Eq.symm (eq_mul_of_mul_inv_eq₀ h₀ (id (Eq.symm h')))


  -- exact
  --   Eq.symm
  --     ((fun {G₀} [GroupWithZero G₀] {a b c} hb ↦ (mul_inv_eq_iff_eq_mul₀ hb).mp) h (id (Eq.symm h')))


-- example (a: ℝ): Πi : Fin (-1), a = 1 := by
--   refine fun i ↦ ?_
  -- apply?

-- lemma lemma2_3_10 (P : RateMatrix) (lambdaP : ℕ → ℝ) (InvariantDistribution P lambdaP) :
--   (∃Λ, Λ > 0, ∀ i, P.Q i (i+1) = Λ) → ∀n, n ≥ 2 → sorry := by
--   sorry

example : Fin (1 - 1) = Fin 0 := by
  rfl

-- example (a b c : ℝ) (h: a = b/c ): a * c = b := by
--   apply div_eq_of_eq_mul

example : (1 : ℕ) ≤ (1 : ℕ) := by
  apply NeZero.one_le

example (a : ℝ) (h : 0 < a) : a ≠ 0 := by
  exact Ne.symm (ne_of_lt h)

example (a : ℝ) (h: a > 0):  0 < a := by
  exact h

example : -1 + 2 = 1 := by
  exact rfl

lemma lemma2_3_help (P : RateMatrix) (lambdaP : ℕ → ℝ) (h: InvariantDistribution P lambdaP) (i : ℕ):
  P.Q (i+2) (i+1) ≠ 0 → lambdaP (i+2) = (((P.Q (i+1) i) + (P.Q (i+1) (i+2)))*(lambdaP (i+1)) - P.Q i (i+1)*lambdaP i)/P.Q (i+2) (i+1) := by
  intro h'''
  rcases h with ⟨h, h', h''⟩
  have h₀: i + 1 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one i)
  have pos_P : 0 < P.Q (i + 2) (i + 1) := by
    have non_neg_P : 0 ≤ P.Q (i + 2) (i + 1) := by
      exact P.departure_rate_greater_than_zero (i + 1) h₀
    exact lt_of_le_of_ne non_neg_P (id (Ne.symm h'''))
    -- apply?
    -- apply P.departure_rate_greater_than_zero (i+1) h₀
  rw [eq_div_iff_mul_eq (ne_of_lt pos_P).symm]
  symm
  rw [tsub_eq_of_eq_add]
  symm

  have h₁ : i = i + 1 - 1 := by
    rfl
  rw [h₁]
  have h₂ : i + 1 - 1 + 2 = (i + 1) + 1 := by
    rfl
  rw [h₂]
  have h₃ : i + 1 - 1 + 1 = i + 1 := by
    rfl
  rw [h₃]
  have h₄ : i + 1 + 1 = (i + 1) + 1 := by
    rfl
  rw [h₄]
  nth_rewrite 1 [add_comm]
  rw [mul_comm]
  nth_rewrite 10 [add_comm]
  apply h (i + 1)
  exact h₀

theorem rewrite (a b c : ℝ) (hab : a = 0 ∨ b = c) : a * b = a * c:= by
    rcases hab with h' | h'
    · rw [h']
      ring
    rw [h']

example (a b c : ℝ) (h : a = 0 ∨ b = c) : a * (b - c) = 0:= by
  apply mul_eq_zero.mpr
  rcases h with e' | f'
  left
  exact e'
  right
  exact sub_eq_zero_of_eq f'

lemma Nat.eq_div_of_cast_eq_div (a b c : ℕ) (h : (a : ℚ) = b / c) : a = b / c := by
  obtain rfl | hc := Nat.eq_zero_or_pos c
  · simp_all
  rw [eq_div_iff (by simp_all [hc.ne'])] at h
  norm_cast at h
  rw [← h, Nat.mul_div_cancel a hc]

example (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) / 2 := by
  apply Nat.eq_div_of_cast_eq_div -- reduce to easier question about rationals
  push_cast
  induction' n with n ih
  · simp
  rw [Finset.sum_Icc_succ_top (by omega), ih]
  push_cast
  ring

example (a b : ℝ) (h : a = b) : a - b = 0 := by
  apply sub_eq_zero_of_eq h

lemma lemma2_3_1 (P : RateMatrix) (lambdaP : ℕ → ℝ) : (InvariantDistribution P lambdaP ∧ ∀i ≠ 0, P.Q i (i-1) ≠ 0) → (∀ i, P.Q i (i+1) ≠ 0) →
  ∀ n, lambdaP n = (∏ i : (Fin n), P.Q (i) (i + 1)/(P.Q (i + 1) i)) * (lambdaP 0) := by
  rintro ⟨h₁, h₂⟩
  intro h
  intro n
  -- rcases h with ⟨Λ, h⟩/
  -- use Λ
  -- intro Λ_pos
  -- intro ns
  induction' n using Nat.twoStepInduction with n ih ih₂
  have h' : (∏ i : (Fin 0), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = (∏ i : (Finset.range (0)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) := by
    exact rfl

  -- Case 0
  rw [h']
  have h'' : (∏ i : (Finset.range (0)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = 1 := by
    apply Finset.prod_range_zero (fun i : ℕ => (P.Q (i) (i + 1) / P.Q (i + 1) i))
  rw[h'']
  ring

  -- Case 1
  rcases h₁ with ⟨h₁, h₁', h₁''⟩
  have h''' : (∏ i : (Fin (1)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = (∏ i ∈ (Finset.range (1)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) := by
    exact rfl
  rw [h''']
  have one_sub_one_eq_zero : (1 : ℕ) - (1 : ℕ) = 0 := by
    exact rfl
  have h''''' : lambdaP 1 = P.Q (0) (0 + 1)/(P.Q (0 + 1) 0)*(lambdaP 0) := by
    rw [mul_comm, ←mul_div_assoc]
    symm
    apply div_eq_of_eq_mul (h₂ 1 Nat.one_ne_zero)
    symm
    rw [one_sub_one_eq_zero]
    -- rw [←h Λ_pos 0]
    nth_rewrite 2 [mul_comm]
    exact h₁'
  have zero_add_one_eq_one : (0 + 1 : ℕ) = (1 :ℕ) := by
    ring
  rw [←zero_add_one_eq_one]
  have succ_range : (∏ i ∈ Finset.range (0+1), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = P.Q (0) (0 + 1) / P.Q (0 + 1) 0 := by
    rw [Finset.prod_range_succ (fun i : ℕ => P.Q (i) (i + 1) / P.Q (↑i + (0 + 1)) ↑i) 0]
    rw [Finset.prod_range_zero]
    ring
  rw [succ_range]
  simp [h''''']

  -- Start of ih proof
  rcases h₁ with ⟨h₁, h₁', h₁''⟩
  have val_gt_1_gt_0 : ∀(i : ℕ), i ≥ 1 → i ≠ 0 := by
    exact fun i a ↦ Nat.ne_zero_of_lt a -- From apply?
  have i_sub_one_gt :  ∀(i : ℕ), i ≥ 2 → i - 1 ≥ 1 := by
    exact fun i a ↦ Nat.le_sub_one_of_lt a
  rw [lemma2_3_help P lambdaP]
  symm
  rw [ih, ih₂]
  have copy1 : (∏ (i : Fin (n+2)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+2)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (i) (i + 1) / P.Q (i + 1) i))

  have copy2 : (∏ (i : Fin (n+1)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+1)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (i) (i + 1) / P.Q (i + 1) i))

  have copy3 : (∏ (i : Fin (n)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n)), P.Q (i) (i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (i) (i + 1) / P.Q (i + 1) i))


  rw [copy1, copy2, copy3]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]

  have h₀: n + 1 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one n)
  have pos_P : 0 < P.Q (n + 2) (n + 1) := by
    have non_neg_P : 0 ≤ P.Q (n + 2) (n + 1) := by
      exact P.departure_rate_greater_than_zero (n + 1) h₀
    have non_zero_P : P.Q (n + 2) (n + 2 - 1) ≠ 0 := by
      apply h₂ (n+2)
      exact Ne.symm (Nat.zero_ne_add_one (n + 1))
    have non_zero_P' : P.Q (n + 2) (n + 1) ≠ 0 := by
      exact non_zero_P

      -- apply?
    exact lt_of_le_of_ne non_neg_P (id (Ne.symm non_zero_P'))
  -- have non_neq_P : 0 < P.Q (n + 2) (n + 1) := by
  --   apply P.departure_rate_greater_than_zero (n+1) h₀
  rw [eq_div_iff_mul_eq (ne_of_lt pos_P).symm]
  nth_rewrite 5 [mul_comm]
  nth_rewrite 8 [mul_comm]
  rw [mul_assoc, mul_assoc]
  rw [mul_assoc, mul_assoc]
  rw [mul_assoc, mul_assoc]

  have rewrite (a b c : ℝ) (hab : a = 0 ∨ b = c) : a * b = a * c:= by
    rcases hab with h' | h'
    · rw [h']
      ring
    rw [h']
  rw [←mul_sub]
  apply rewrite (∏ x ∈ Finset.range n, P.Q (x) (x + 1) / P.Q (x + 1) x)
  right
  have rewrite2 : P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n + 1) (n + 1 + 1) / P.Q (n + 1 + 1) (n + 1) * (lambdaP 0 * P.Q (n + 2) (n + 1))) = (lambdaP 0) * (P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n+1) (n + 1+1) / P.Q (n + 1 + 1) (n + 1) * P.Q (n + 2) (n + 1))) := by
    ring

  have rewrite3 : P.Q (n) (n + 1) / P.Q (n + 1) n * (lambdaP 0 * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))) - lambdaP 0 * P.Q n (n + 1) = (lambdaP 0) * (P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))- P.Q n (n + 1)) := by
    ring
  rw [rewrite2, rewrite3]
  apply rewrite
  right
  have rewrite4 : n + 1 + 1 = n + 2 :=by
    ring
  rw [rewrite4]
  -- rw [h, h]
  rw [div_eq_mul_one_div]
  nth_rewrite 3 [←mul_one (P.Q (n) (n + 1))]
  have rewrite5 : P.Q (n) (n + 1) * (1 / P.Q (n + 1) n) * (P.Q (n + 1) n + P.Q (n+1) (n + 1+1)) - P.Q (n) (n + 1) * 1 = P.Q (n) (n + 1) * ((1 / P.Q (n + 1) n) * (P.Q (n + 1) n + P.Q (n+1) (n + 1+1)) - 1) := by
    ring
  rw [rewrite5]
  rw [mul_assoc]
  rw [div_mul_cancel₀]
  apply rewrite
  right
  rw [mul_add]
  rw [div_mul_cancel₀]
  ring
  -- We proved the difficult part!!!!
  -- Now just some cleaning up
  apply h₂
  exact h₀
  apply h₂
  exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  -- exact Λ_pos
  -- exact Λ_pos
  constructor
  exact h₁
  constructor
  exact h₁'
  exact h₁''
  have non_zero_P : P.Q (n + 2) (n + 2 - 1) ≠ 0 := by
      apply h₂ (n+2)
      exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  exact non_zero_P

-- example : 1 ≠ 0 := by
--   exact Nat.one_ne_zero

example (n m : ℕ) : n = m ∨ n ≠ m := by
  exact eq_or_ne n m

lemma lemma2_3_3a' (P : RateMatrix) (lambdaP : ℕ → ℝ) : (InvariantDistribution P lambdaP) →
  -- (∃ k : ℕ, ∀i, i ≠ 0 ∧ i < k → P.Q i (i-1) ≠ 0) → (∃ k : ℕ, ∀i, i < k → P.Q i (i+1) ≠ 0) →
  ∀k : ℕ, (∀i, i ≠ 0 ∧ i < k → P.Q i (i-1) ≠ 0) ∧ (∀i, i < k → P.Q i (i+1) ≠ 0)→ ∀ n, n < k →
   lambdaP n = (∏ i : (Fin n), (P.Q i (i+1))/(P.Q (i + 1) i)) * (lambdaP 0) := by
  intro h₁ k
  rintro ⟨h, h₂⟩
  -- have copy : ∀i, i < k → (i ≠ 0 → P.Q i (i-1) ≠ 0) ∧ P.Q i (i+1) ≠ 0 := by
  --   intro i_lt_k
    -- refine fun i a ↦ ?_

  intro n n_pos
  rcases h₁ with ⟨h₁, h₁', h₁''⟩

  -- intro i i_lt_k
  -- have h₁ : (∃ k : ℕ, ∀i, i ≠ 0 ∧ i < k → P.Q i (i-1) ≠ 0) := by
  --   have h₁help : (∀ j, (j < k ∧ j ≠ 0) → P.Q j (j-1) ≠ 0) := by
  --     intro j
  --     rintro ⟨h, h'⟩
  --     rcases eq_or_ne j i with h | h
  --     · rw [←h] at h₁'
  --       apply h₁' h'

      -- rcases
      -- apply?
    -- use k
    -- intro i'
    -- rintro ⟨h'', h'''⟩
    -- apply h₁' h''
  -- have
  -- rintro ⟨h₁, h₂, h₃⟩


  -- rcases h with ⟨k, h⟩
  -- intro h'
  -- rcases h' with ⟨Λ, h'⟩
  -- use k
  -- intro n n_pos
  -- use Λ
  -- intro Λ_pos
  -- have hypothes: ∀ (i : ℕ), P.Q i (i + 1) = Λ := by
  --   exact fun i ↦ h' Λ_pos i



  -- use k
  -- use Λ


  -- rcases h' with ⟨k_pos, h'⟩
  -- use Λ
  -- intro Λ_pos n
  induction' n using Nat.twoStepInduction with n ih ih₂
  have h' : (∏ i : (Fin 0), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = (∏ i : (Finset.range (0)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) := by
    exact rfl

  -- Case 0
  rw [h']
  have h'' : (∏ i : (Finset.range (0)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = 1 := by
    apply Finset.prod_range_zero (fun i : ℕ => (P.Q (↑i) (↑i + 1) / P.Q (i + 1) i))
  rw[h'']
  ring

  -- Case 1
  -- rcases (h₁ 1 Nat.one_ne_zero) with ⟨h₁, h₁', h₁''⟩
  have h''' : (∏ i : (Fin (1)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = (∏ i ∈ (Finset.range (1)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) := by
    exact rfl
  rw [h''']
  have one_sub_one_eq_zero : (1 : ℕ) - (1 : ℕ) = 0 := by
    exact rfl
  have h''''' : lambdaP 1 = P.Q (0) (0 + 1)/(P.Q (0 + 1) 0)*(lambdaP 0) := by
    rw [mul_comm, ←mul_div_assoc]
    symm
    -- have neq_zero:  P.Q (0 + 1) 0 ≠ 0:= by
    --   apply h 1 ⟨Nat.one_ne_zero, n_pos⟩
    apply div_eq_of_eq_mul (h 1 ⟨Nat.one_ne_zero, n_pos⟩)
    symm
    rw [one_sub_one_eq_zero]
    -- rw [←hypothes 0]
    nth_rewrite 2 [mul_comm]
    assumption
  have zero_add_one_eq_one : (0 + 1 : ℕ) = (1 :ℕ) := by
    ring
  rw [←zero_add_one_eq_one]
  have succ_range : (∏ i ∈ Finset.range (0+1), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = P.Q 0 (0+1) / P.Q (0 + 1) 0 := by
    rw [Finset.prod_range_succ (fun i : ℕ => P.Q (↑i) (↑i + 1) / P.Q (↑i + (0 + 1)) ↑i) 0]
    rw [Finset.prod_range_zero]
    ring
  rw [succ_range]
  simp [h''''']

  -- Start of ih proof
  -- rcases h₁ with ⟨h₁, h₁', h₁''⟩
  have val_gt_1_gt_0 : ∀(i : ℕ), i ≥ 1 → i ≠ 0 := by
    exact fun i a ↦ Nat.ne_zero_of_lt a -- From apply?
  have i_sub_one_gt :  ∀(i : ℕ), i ≥ 2 → i - 1 ≥ 1 := by
    exact fun i a ↦ Nat.le_sub_one_of_lt a
  rw [lemma2_3_help P lambdaP]
  symm
  rw [ih, ih₂]
  have copy1 : (∏ (i : Fin (n+2)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+2)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (↑i) (↑i + 1) / P.Q (i + 1) i))

  have copy2 : (∏ (i : Fin (n+1)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+1)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (↑i) (↑i + 1) / P.Q (i + 1) i))

  have copy3 : (∏ (i : Fin (n)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n)), P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (P.Q (↑i) (↑i + 1) / P.Q (i + 1) i))


  rw [copy1, copy2, copy3]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]

  have h₀: n + 1 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one n)
  have pos_P : 0 < P.Q (n + 2) (n + 1) := by
    have non_neg_P : 0 ≤ P.Q (n + 2) (n + 1) := by
      exact P.departure_rate_greater_than_zero (n + 1) h₀
    have non_zero_P : P.Q (n + 2) (n + 2 - 1) ≠ 0 := by
      have non_zero : n+2 ≠ 0 := by
        exact Ne.symm (Nat.zero_ne_add_one (n + 1))
      apply h (n+2) ⟨non_zero, n_pos⟩
      -- exact Ne.symm (Nat.zero_ne_add_one (n + 1))
    have non_zero_P' : P.Q (n + 2) (n + 1) ≠ 0 := by
      exact non_zero_P

      -- apply?
    exact lt_of_le_of_ne non_neg_P (id (Ne.symm non_zero_P'))
  -- have non_neq_P : 0 < P.Q (n + 2) (n + 1) := by
  --   apply P.departure_rate_greater_than_zero (n+1) h₀
  rw [eq_div_iff_mul_eq (ne_of_lt pos_P).symm]
  nth_rewrite 5 [mul_comm]
  nth_rewrite 8 [mul_comm]
  rw [mul_assoc, mul_assoc]
  rw [mul_assoc, mul_assoc]
  rw [mul_assoc, mul_assoc]

  have rewrite (a b c : ℝ) (hab : a = 0 ∨ b = c) : a * b = a * c:= by
    rcases hab with h' | h'
    · rw [h']
      ring
    rw [h']
  rw [←mul_sub]
  apply rewrite (∏ x ∈ Finset.range n, P.Q (x) (x + 1) / P.Q (x + 1) x)
  right
  have rewrite2 : P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n+1) (n + 1+1) / P.Q (n + 1 + 1) (n + 1) * (lambdaP 0 * P.Q (n + 2) (n + 1))) = (lambdaP 0) * (P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n+1) (n + 1+1) / P.Q (n + 1 + 1) (n + 1) * P.Q (n + 2) (n + 1))) := by
    ring

  have rewrite3 : P.Q (n) (n + 1) / P.Q (n + 1) n * (lambdaP 0 * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))) - lambdaP 0 * P.Q n (n + 1) = (lambdaP 0) * (P.Q (n) (n + 1) / P.Q (n + 1) n * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))- P.Q n (n + 1)) := by
    ring
  rw [rewrite2, rewrite3]
  apply rewrite
  right
  have rewrite4 : n + 1 + 1 = n + 2 :=by
    ring
  rw [rewrite4]
  -- rw [h', h']
  rw [div_eq_mul_one_div]
  nth_rewrite 3 [←mul_one (P.Q (n) (n + 1))]
  have rewrite5 : P.Q (n) (n + 1) * (1 / P.Q (n + 1) n) * (P.Q (n + 1) n + P.Q (n+1) (n + 2)) - (P.Q (n) (n + 1)) * 1 = P.Q (n) (n + 1) * ((1 / P.Q (n + 1) n) * (P.Q (n + 1) n + P.Q (n+1) (n + 2)) - 1) := by
    ring
  rw [rewrite5]
  rw [mul_assoc]
  rw [div_mul_cancel₀]
  apply rewrite
  right
  rw [mul_add]
  rw [div_mul_cancel₀]
  ring
  -- We proved the difficult part!!!!
  -- Now just some cleaning up
  apply h (n+1)
  constructor
  · exact h₀
  exact Nat.lt_of_succ_lt n_pos
  apply h (n+2)
  constructor
  · exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  exact n_pos

    -- ⟨apply?, ⟩
  -- exact h₀
  -- apply h₂
  -- exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  -- exact Λ_pos
  -- exact Λ_pos
  -- constructor
  exact Nat.lt_of_succ_lt n_pos
  exact Nat.lt_of_add_right_lt n_pos
  exact ⟨h₁, h₁', h₁''⟩
  apply h (n+2)
  constructor
  · exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  exact n_pos

  -- apply h (n+2)
  -- constructor
  -- · exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  -- exact n_pos
  -- exact h₁
  -- constructor
  -- exact h₁'
  -- exact h₁''
  -- have non_zero_P : P.Q (n + 2) (n + 2 - 1) ≠ 0 := by
  --     apply h₂ (n+2)
  --     exact Ne.symm (Nat.zero_ne_add_one (n + 1))
  -- exact non_zero_P

-- #print axioms lemma2_3_1

-- lemma lemma2_3_1_a (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) : (∀i ≠ 0, P.Q i (i-1) ≠ 0) ∧ (∃Λ, Λ > 0 → ∀ i, P.Q i (i+1) = Λ) →
--   (∃ Λ, Λ > 0 → lambdaP 0 = 1/(∑'n, (∏ i : (Fin (n-1)), Λ/(P.Q (i + 1) i)))) := by
--   intro h₁
--   rcases h₁ with ⟨h₁, h₂⟩
--   rcases h₂ with ⟨Λ, h₂⟩
  -- rintro Λ_pos with ⟨Λ_pos, a⟩s

  -- rintro h₁ with ⟨i, h₁⟩
  -- have h₁ (n : ℕ): lambdaP n = (∏ i : (Fin n), Λ/(P.Q (i + 1) i)) * (lambdaP 0) := by
  --   apply lemma2_3_1 P lambdaP

  -- use Λ
  -- intro Λ_pos

  -- have conjunction : InvariantDistribution P lambdaP ∧ ∀ (i : ℕ), i ≠ 0 → P.Q i (i - 1) ≠ 0 := by
  --   constructor
  --   exact h
  --   exact h₁
  -- have h₂' : ∃ Λ, Λ > 0 → ∀ (i : ℕ), P.Q i (i + 1) = Λ := by
  --   use Λ

  -- have h₁ (n : ℕ): lambdaP n = (∏ i : (Fin n), Λ/(P.Q (i + 1) i)) * (lambdaP 0) := by
  --    refine lemma2_3_1 P lambdaP conjunction h₂'

  -- rcases h with ⟨h, h', h''⟩
  -- rw [lemma2_3_1 ] at h''

-- example (n k : ℝ) (h : n < k) : k ≰ n := by
--   apply?

example (m n : ℕ) : m > n → m = n + 1 ∨ m > n + 1 := by
  intro h
  exact eq_or_gt_of_le h

example (m n : ℕ) : m  + 1 > n → m ≥ n := by
  exact fun a ↦ Nat.le_of_lt_succ a

example (m n : ℕ) : m ≥ n → m = n ∨ m > n := by
  exact fun a ↦ LE.le.eq_or_gt a
  -- exact LE.le.eq_or_gt h

example (m n : ℕ) : m = n ↔ m ≥ n ∧ m ≤ n := by
  exact Iff.symm antisymm_iff

lemma lemma2_3_3a (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) :
  ∀n, n ≠ 0 → ∀k, k > n → (∀m, (n < m ∧ m < k) → P.Q (m-1) m ≠ 0 ∧ P.Q m (m-1) ≠ 0) → P.Q n (n-1) = 0 ∧ P.Q k (k-1) = 0 → lambdaP (n-1) = 0 →
  ∀m', (n < m' ∧ m' < k) → lambdaP m' = (∏i : (Fin (m'-n)), (P.Q (i + n) (i+n+1))/(P.Q (i+n+1) (i+n))) * lambdaP n := by
  intro n n_non_zero k k_gt_n inbetween_non_zero ⟨n_zero_dep, k_zero_dep⟩ lambda_n_zero
  intro m' mp_bt_n_k
  -- rcases m_bt_n_k with ⟨m_gt_n, m_lt_k⟩
  rcases mp_bt_n_k with ⟨mp_gt_n, mp_le_k⟩
  induction' m' using Nat.twoStepInduction with m' ih ih₂
  · by_contra g
    exact Nat.not_succ_le_zero n mp_gt_n

  · have h : n = 0 := by
      exact Nat.lt_one_iff.mp mp_gt_n
    contradiction
  have fin_eq_range : (∏ i : (Fin (k - n)), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (k - n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    exact Eq.symm (Finset.prod_range fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))

  have cases : m' + 1 < n ∨ m' + 1 = n ∨ m' + 1 = n + 1 ∨ m' + 1 > n + 1 := by
    have cases' : (m' + 1 < n ∨ m' + 1 = n) ∨ m' + 1 > n := by
      refine or_assoc.mpr ?_
      exact Nat.lt_trichotomy (m' + 1) n

    have cases'' : m' + 1 > n → (m' = n ∨ m' > n) := by
      · intro h
        apply (fun a ↦ Nat.le_of_lt_succ a) at h
        simp
        apply LE.le.eq_or_gt h

    have cases''' : (m' + 1 < n ∨ m' + 1 = n) ∨ m' + 1 > n → (m' + 1 < n ∨ m' + 1 = n) ∨ (m' = n ∨ m' > n) := by
      intro h
      exact Or.symm (Or.imp_left cases'' (id (Or.symm cases')))
    refine or_assoc.mp ?_
    simp
    apply cases'''
    exact cases'

  rcases cases with mp_add_one_lt_n | mp_add_one_eq_n | mp_add_one_eq_n_add_one | mp_add_one_gt_n_add_one
  · by_contra
    have hypo: n < m' + 2 → n ≤ m' + 1 := by
      intro h
      exact Nat.le_of_lt_succ mp_gt_n
    apply hypo at mp_gt_n
    have hypo2 : n ≤ m' + 1 → ¬ (n > m' + 1) := by
      exact fun a ↦ (fun {a b} ↦ Nat.not_lt.mpr) mp_gt_n
    apply hypo2
    exact mp_gt_n
    exact mp_add_one_lt_n

  · have hypo : m' + 2 - n = 0 + 1 := by
      have hypo : m' + 2 - n = m' + 1 + 1 - n := by
        ring
      rw [hypo]
      rw [mp_add_one_eq_n]
      ring
      omega
    rw [hypo]
    have hypo' : (∏ i : Fin (1), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (1), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
      exact rfl
    rw [hypo']
    rw [Finset.prod_range_succ]
    rw [Finset.prod_range_zero]
    rw [lemma2_3_help P lambdaP]
    have hypo'' : m' = n - 1 := by
      exact Nat.eq_sub_of_add_eq mp_add_one_eq_n
    rw [hypo'']
    rw [lambda_n_zero]
    simp
    have hypo''' : n - 1 + 1 = n := by
      exact Nat.succ_pred_eq_of_ne_zero n_non_zero
    rw [hypo''']
    have hypo'''' : n - 1 + 2 = n + 1 := by
      exact Eq.symm ((fun {m k n} ↦ Nat.add_right_cancel_iff.mpr) (id (Eq.symm hypo''')))
    rw [hypo'''']
    have h1 : (P.Q n (n - 1) + P.Q n (n + 1)) * lambdaP n / P.Q (n + 1) n = lambdaP n * (P.Q n (n - 1) + P.Q n (n + 1))/P.Q (n + 1) n := by
      rw [div_eq_mul_one_div]
      nth_rewrite 2 [div_eq_mul_one_div]
      ring
    rw [h1]
    nth_rewrite 2 [mul_comm]
    rw [mul_div_assoc]
    apply rewrite
    right
    rw [n_zero_dep]
    ring
    exact h
    have non_zero_P :  ∀ (l : ℕ), n < l ∧ l < k → P.Q l (l-1) ≠ 0 := by
      intro l h
      apply (inbetween_non_zero l h).right
    have mp_between : n < m' + 2 ∧ m' + 2 < k := by
      exact ⟨mp_gt_n, mp_le_k⟩
    apply non_zero_P (m'+2) mp_between
  · simp at mp_add_one_eq_n_add_one
    have hypo : m' + 2- n = 2 := by
      rw [mp_add_one_eq_n_add_one]
      exact Nat.add_sub_self_left n 2
    rw [hypo]
    rw [mp_add_one_eq_n_add_one]
    rw [lemma2_3_help P lambdaP]
    have hypo' : (∏ i : Fin 2, P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range 2, P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
      exact rfl
    rw [hypo']
    repeat rw [Finset.prod_range_succ]
    rw [Finset.prod_range_zero]
    have n_le_mp_add_one : n ≤ m' := by
      exact Nat.le_of_eq (id (Eq.symm mp_add_one_eq_n_add_one))
    have n_lt_mp_add_one : n < m' + 1 := by
      exact Order.lt_add_one_iff.mpr n_le_mp_add_one

    have k_geq_mp_add_one : k > m' + 1 := by
      exact Nat.lt_of_succ_lt mp_le_k

    nth_rewrite 5 [←mp_add_one_eq_n_add_one]
    rw [ih₂ n_lt_mp_add_one k_geq_mp_add_one]
    have hypo'' : m' + 1- n = 1 := by
      rw [mp_add_one_eq_n_add_one]
      exact Nat.add_sub_self_left n 1
    rw [hypo'']
    have hypo''' : (∏ i : Fin 1, P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range 1, P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
      exact rfl
    rw [hypo''']
    repeat rw [Finset.prod_range_succ]
    rw [Finset.prod_range_zero]
    simp
    have hypo1 : ((P.Q (n + 1) n + P.Q (n + 1) (n + 2)) * (P.Q n (n + 1) / P.Q (n + 1) n * lambdaP n) - P.Q n (n + 1) * lambdaP n) / P.Q (n + 2) (n + 1) = lambdaP n * (((P.Q (n + 1) n + P.Q (n + 1) (n + 2)) * (P.Q n (n + 1) / P.Q (n + 1) n) - P.Q n (n + 1)) / P.Q (n + 2) (n + 1)) := by
      nth_rewrite 1 [mul_comm]
      repeat rw [←mul_assoc]
      nth_rewrite 2 [mul_comm]
      nth_rewrite 3 [mul_comm]
      repeat rw [mul_assoc]
      rw [←mul_sub (lambdaP n)]
      ring
    rw [hypo1]
    nth_rewrite 3 [mul_comm]
    rw [rewrite]
    right
    have hypo2 : 1 + n + 1 = n + 2 := by
      ring
    rw [hypo2]
    have hypo3 : 1 + n = n + 1 := by
      ring
    rw [hypo3]
    rw [div_eq_mul_one_div]
    nth_rewrite 4 [div_eq_mul_one_div]
    nth_rewrite 1 [mul_comm]
    repeat rw [←mul_assoc]
    nth_rewrite 3 [mul_comm]
    rw [rewrite]
    right
    rw [add_mul]
    rw [div_eq_mul_one_div]
    repeat rw [←mul_assoc]
    nth_rewrite 4 [mul_comm]
    nth_rewrite 2 [mul_comm]
    repeat rw [mul_assoc]
    repeat rw [mul_assoc]
    rw [←mul_add]
    nth_rewrite 2 [←mul_one (P.Q n (n + 1))]
    rw [←mul_sub]
    rw [rewrite]
    right
    rw [←div_eq_mul_one_div]
    rw [div_self]
    ring
    rw [←mp_add_one_eq_n_add_one]
    have all_between_dep_nonzero : ∀ (m : ℕ), n < m ∧ m < k → P.Q (m) (m-1) ≠ 0 := by
      intro m h
      apply (inbetween_non_zero m h).right
    have hypo5 : m' + 1 < k := by
      exact k_geq_mp_add_one
    apply all_between_dep_nonzero (m' + 1)

    constructor
    · apply n_lt_mp_add_one
    apply hypo5
    exact h

    have non_zero_P :  ∀ (l : ℕ), n < l ∧ l < k → P.Q l (l-1) ≠ 0 := by
      intro l h
      apply (inbetween_non_zero l h).right
    have mp_between : n < m' + 2 ∧ m' + 2 < k := by
      exact ⟨mp_gt_n, mp_le_k⟩
    have n_between : n < n + 2 ∧ n + 2 < k := by
      rw [mp_add_one_eq_n_add_one] at mp_between
      assumption
      -- exact ⟨mp_gt_n, mp_le_k⟩
    apply non_zero_P (n+2) n_between

  rw [lemma2_3_help P lambdaP]
  rw [ih]
  rw [ih₂]
  have lambda_up_front : (P.Q (m' + 1) m' + P.Q (m' + 1) (m' + 2)) * ((∏ i : (Fin (m' - n)), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) * lambdaP n) - P.Q m' (m' + 1) * ((∏ i : Fin (m' - n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) * lambdaP n) = lambdaP n * ((P.Q (m' + 1) m' + P.Q (m' + 1) (m' + 2)) * ((∏ i : (Fin (m' - n)), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n))) - P.Q m' (m' + 1) * ((∏ i : Fin (m' - n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)))) := by
    rw [←mul_assoc, mul_comm]
    repeat rw [←mul_assoc]
    nth_rewrite 3 [mul_comm]
    repeat rw [mul_assoc]
    rw [←mul_sub]

  have copy1 : (∏ i : Fin (m'-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (m'-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    exact Eq.symm (Finset.prod_range fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))

  have copy2 : (∏ i : Fin (m'+1-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (m'+1-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    exact Eq.symm (Finset.prod_range fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))

  have copy3 : (∏ i : Fin (m'+2-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (m'+2-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    exact Eq.symm (Finset.prod_range fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))

  rw [copy1, copy2, copy3]

  have mp_add_one_sub_n_eq_mp_sub_n_add_one : m' + 1 - n = (m' - n) + 1 := by
    have h'' : m' > n  := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    have h' : n ≤ m' := by
      exact Nat.le_of_succ_le h''
    ring
    rw [Nat.add_sub_assoc h']
  rw [mp_add_one_sub_n_eq_mp_sub_n_add_one]
  rw [Finset.prod_range_succ]

  have mp_add_two_sub_n_eq_mp_sub_n_add_two : m' + 2 - n = (m' - n) + 2 := by
    have h'' : m' > n  := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    have h' : n ≤ m' := by
      exact Nat.le_of_succ_le h''
    ring
    rw [Nat.add_sub_assoc h']
  rw [mp_add_two_sub_n_eq_mp_sub_n_add_two]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]
  repeat rw [←mul_assoc]
  nth_rewrite 3 [mul_comm]
  repeat rw [mul_assoc]
  nth_rewrite 4 [mul_comm]
  repeat rw [mul_assoc]
  rw [←mul_sub (∏ x ∈ Finset.range (m' - n), P.Q (x + n) (x + n + 1) / P.Q (x + n + 1) (x + n))]
  rw [div_eq_mul_one_div]
  repeat rw [mul_assoc]
  apply rewrite
  right
  have hypo6 : m' - n + n + 1 = m' + 1 := by
    refine Nat.add_right_cancel_iff.mpr ?_
    refine Nat.sub_add_cancel ?_
    have hypo7 : m' > n := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    exact Nat.le_of_succ_le hypo7
  rw [hypo6]
  have hypo7 : m' - n + 1 + n = m' + 1 := by
    refine
      Eq.symm
        ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ mp_add_one_sub_n_eq_mp_sub_n_add_one)
    have hypo' : m' > n := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    exact Nat.le_of_lt_succ mp_gt_n
  rw [hypo7]
  have mp_add_add_eq_mp_two : m' + 1 + 1 = m' + 2 := by
    ring
  rw [mp_add_add_eq_mp_two]
  have hypo8 : m' - n + n = m' := by
    exact Eq.symm ((fun {a b} ↦ Nat.succ_inj'.mp) (id (Eq.symm hypo6)))
  repeat rw [←mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [←mul_sub]
  nth_rewrite 4 [mul_comm]
  repeat rw [mul_assoc]
  apply rewrite
  right
  rw [hypo8]
  rw [div_eq_mul_one_div]
  nth_rewrite 4 [div_eq_mul_one_div]
  rw [add_mul]
  nth_rewrite 3 [mul_comm]
  repeat rw [←mul_assoc]
  nth_rewrite 2 [←div_eq_mul_one_div]
  rw [div_self]
  rw [one_mul]
  ring

  -- Main proof accepted just some clean-up to do :)
  have all_between_dep_nonzero : ∀ (m : ℕ), n < m ∧ m < k → P.Q (m) (m-1) ≠ 0 := by
    intro m h
    apply (inbetween_non_zero m h).right
  have hypo5 : m' + 1 < k := by
    exact Nat.lt_of_succ_lt mp_le_k
    -- exact mp_le_k
  apply all_between_dep_nonzero (m' + 1)

  have n_lt_mp_add_one : m' + 1 > n := by
    have helper : m' > n := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    exact Nat.lt_add_right 1 helper

  constructor
  · apply n_lt_mp_add_one
  exact hypo5

  have n_lt_mp_add_one : m' + 1 > n := by
    have helper : m' > n := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    exact Nat.lt_add_right 1 helper

  exact n_lt_mp_add_one
  exact Nat.le_of_succ_le mp_le_k
  exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
  have mp_lt_k : m' < k := by
    have mp_add_one_le_k : m' + 1 ≤ k := by
      linarith [mp_le_k]
      -- exact mp_le_k
      -- apply?
    exact mp_add_one_le_k
    -- exact Nat.le_of_succ_le mp_add_one_le_k
    -- exact Nat.le_of_add_right_le mp_le_k
  exact mp_lt_k
  exact h
  have non_zero_P :  ∀ (l : ℕ), n < l ∧ l < k → P.Q l (l-1) ≠ 0 := by
      intro l h
      apply (inbetween_non_zero l h).right
  have mp_between : n < m' + 2 ∧ m' + 2 < k := by
    exact ⟨mp_gt_n, mp_le_k⟩
  apply non_zero_P (m'+2) mp_between


-- lemma lemma2_3_3b (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) {m : ℕ}
--   (A : {n : (Fin m) // (P.Q n (n-1) ≠ 0) ∧ Fin.toNat n ≠ 0}) : ∀ (i : Fin m), i ∈ A → Fin.toNat i ≠ 1 → lambdaP (i-1) = 0, 1=1 := by
--   sorry


lemma fin_add_eq_non_add (n : ℕ) (n_non_zero : n ≠ 0): Fin (n - 1 + 1) = Fin n := by
  have  h:  n - 1 + 1 = n := by
    refine Nat.sub_add_cancel ?_
    exact Nat.one_le_iff_ne_zero.mpr n_non_zero
  rw [h]

lemma n_sub_one_add_one_eq_n (n : ℕ) (n_non_zero : n ≠ 0) : n - 1 + 1 = n := by
  refine Nat.sub_add_cancel ?_
  exact Nat.one_le_iff_ne_zero.mpr n_non_zero

-- lemma ele_of_wrong_fin_eq_other_fin (n : ℕ) (n_non_zero : n ≠ 0) : ∀ i : Fin (n - 1 + 1) →  i :  Fin (n) := by
  -- refine type_eq_of_heq ?_

local notation "mycast("a","b","c")" => (Fin.cast (n_sub_one_add_one_eq_n a b) (Fin.castSucc c))
local notation "mycast'("a","b","c")" => (Fin.cast (n_sub_one_add_one_eq_n a b) c)

example (n : ℕ) (h : n -1 = 0) : n = 1 ∨ n = 0 := by
  have basically_goal : n ≤ 1 := by
    exact Nat.le_of_sub_eq_zero h
  have helper :  ¬n > 1 := by
    exact Nat.not_lt.mpr basically_goal
  rcases lt_trichotomy n 1 with a | b | c
  · right
    exact Nat.lt_one_iff.mp a
  left
  assumption
  contradiction

  -- right
  -- exact Or.symm ((fun {n} ↦ Nat.le_one_iff_eq_zero_or_eq_one.mp) basically_goal)

  -- have asd: n -1 +1 = 1 := by
  --   exact Nat.add_left_eq_self.mpr h

  -- constructor/
  -- · apply?
lemma helper_lema (i : ℕ) {n : ℕ} (h : i < n - 1) : i < n := by
  exact Nat.lt_of_lt_pred h

lemma helper_lema' (i : ℕ) {n : ℕ} (h : i < n - 1) : i + 1 < n := by
  exact Nat.add_lt_of_lt_sub h

-- example (n : ℕ) (h: n < n) : false := by
--   linarith [h]

-- example (n m : ℕ) : n < m ∧ n + 1 > m → false := by
--   intro ⟨a, b⟩
--   have negation : ¬(n + 1 ≤ m) := by
--     exact Nat.not_le_of_lt b
--   contradiction

-- example (i : ℕ) : i = 0 ∨ i > 0 := by
--   exact Nat.eq_zero_or_pos i
  -- exact False.elim dfwsg
  -- exact False.elim dfwsg
-- example (i : ℕ) (h : i - 1 =0): i =0 ∨ i = 1 := by
--   refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
--   exact Nat.le_of_sub_eq_zero h

-- example (n m : ℕ)(a : n > 0) (b : m > 0) : (n>0) ∧ (m>0) := by
--   exact ⟨a, b⟩

lemma lemma2_3_3b (P : RateMatrix) (lambdaP : ℕ → ℝ) (h'' :InvariantDistribution P lambdaP) (n : ℕ) [NeZero n] (n_non_zero: n ≠ 0) (A : Fin n → ℕ)
  (Indices_props : (∀i : ℕ, (h : i < n-1) → (A ⟨i, (helper_lema i h)⟩  ≠ 0→
  P.Q (A ⟨i, (helper_lema i h)⟩) (A ⟨i, (helper_lema i h)⟩-1) = 0) ∧ (A ⟨i, (helper_lema i h)⟩) < (A ⟨i+1, helper_lema' i h⟩)) ∧
  P.Q (A mycast'(n,n_non_zero,(Fin.last (n-1)))) (A mycast'(n,n_non_zero,Fin.last (n-1)) - 1) = 0) :
  (∀i : ℕ, P.Q i (i+1) ≠ 0) → (∀m : ℕ, m ≠ 0 ∧ P.Q (m) (m-1) = 0 → ∃i : Fin (n), m = A i) → ∀ i : Fin n, A i ≠ 0 → lambdaP ((A i)-1) = 0 := by
  intro pos_arrival
  intro no_missed_vals
  -- rcases h with ⟨a, h⟩
  have all_i_non_zero_bigger_A : ∀ i : (Fin n), ∀ j : (Fin n), i > j → A i > (A j) := by
    intro i j h''
    rcases i with ⟨i, i_fin⟩
    rcases j with ⟨j, j_fin⟩
    -- have ifin_eq_jfin : i_fin = j_fin := by
    --   exact
    induction' i with i ih
    · induction' j with j jh
      · contradiction
      contradiction
    induction' j with j jh
    -- have h''' : (i+1) < (n-1) ∨ i+1 = n-1 ∨ i+1 > n-1 := by
    --   apply lt_trichotomy (i+1) (n-1)
    rcases (lt_trichotomy (i+1) (n-1)) with h | h | h
    · have i_in_fin : ∃ m : Fin (n-1), m = i + 1 := by
        exact CanLift.prf (i + 1) h
      rcases (lt_trichotomy (n-1) (1)) with h' | h' | h'
      · have n_lt_2 : n < 2 := by
          exact (Nat.sub_lt_sub_iff_right j_fin).mp h'
        have i_lt_1 : i + 1 < 1 := by
          exact Nat.lt_trans h h'
        have i_lt_0 : i < 0 := by
          exact Nat.succ_lt_succ_iff.mp i_lt_1
        contradiction
      · rw [h'] at h
        have i_lt_0 : i < 0 := by
          exact Nat.succ_lt_succ_iff.mp h
        contradiction
      · have n_sub_one_neq_zero : n-1 ≠ 0 := by
         exact Nat.ne_zero_of_lt h
        have n_ne_zero : NeZero (n-1) := by
          exact { out := n_sub_one_neq_zero }
        have fin_nat_i_eq_i : Fin.ofNat' (n-1) (i) = i := by
          exact rfl
        have i_fin' : i < n -1:= by
          exact Nat.lt_sub_of_add_lt i_fin
        have i_fin'' : i < n := by
          exact helper_lema i i_fin'
        have i_lt_pred' : A ⟨i + 1, i_fin⟩ > A ⟨i, i_fin''⟩ := by
          apply (Indices_props.left i i_fin').right
        rcases Nat.eq_zero_or_pos i with h''' | h'''
        · have equal : (⟨i, i_fin''⟩ : Fin n) = ⟨0, j_fin⟩ := by
            exact Fin.mk.inj_iff.mpr h'''
          rw [equal] at i_lt_pred'
          assumption
        have i_add_gt_0 : A ⟨i, i_fin''⟩ > A ⟨0, j_fin⟩ := by
          exact ih i_fin'' h'''
        exact Nat.lt_trans (ih i_fin'' h''') i_lt_pred'
    have i_fin' : i < n :=by
      exact Nat.lt_of_succ_lt i_fin
    have i_fin'' : i < n-1  := by
      exact Nat.lt_sub_of_add_lt i_fin
    have i_add_one_gt_i : A ⟨i + 1, i_fin⟩ > A ⟨i, i_fin'⟩ := by
      apply (Indices_props.left i i_fin'').right
    · rcases Nat.eq_zero_or_pos i with h''' | h'''
      · have equal : (⟨i, i_fin'⟩ : Fin n) = ⟨0, j_fin⟩ := by
          exact Fin.mk.inj_iff.mpr h'''
        rw [equal] at i_add_one_gt_i
        assumption
      have i_gt_j : (⟨i, i_fin'⟩ : Fin n) > ⟨0, j_fin⟩ := by
        exact h'''
      have gt_zero : A ⟨i, i_fin'⟩ > A ⟨0, j_fin⟩ := by
        apply ih i_fin' i_gt_j
      exact Nat.lt_trans (ih i_fin' h''') i_add_one_gt_i
    · have hypo : n < i + 2 := by
        exact (Nat.sub_lt_sub_iff_right j_fin).mp h
      have negation : ¬(i + 2 ≤ n) := by
        exact Nat.not_le_of_lt hypo
      contradiction
    have i_fin' : i < n :=by
      exact Nat.lt_of_succ_lt i_fin
    have i_fin'' : i < n-1  := by
      exact Nat.lt_sub_of_add_lt i_fin
    have j_fin' : j < n := by
      exact Nat.lt_of_succ_lt j_fin
    rcases Nat.eq_zero_or_pos i with h''' | h'''
    · have equal' : (⟨i, i_fin'⟩ : Fin n) > ⟨j, j_fin'⟩ := by
        exact Fin.succ_lt_succ_iff.mp h''
      have i_gt_0 : i > 0 := by
        exact Nat.zero_lt_of_lt equal'
      have i_neq_0 : i ≠ 0 := by
        exact Nat.ne_zero_of_lt equal'
      contradiction

    rcases (lt_trichotomy (i) (j+1)) with h | h | h
    · have i_gt_j : i > j := by
        exact Nat.succ_lt_succ_iff.mp h''
      have neg : ¬(i ≤ j) := by
        exact Nat.not_le_of_lt i_gt_j
      have neg' : ¬(i < j + 1) := by
        exact Nat.not_lt.mpr i_gt_j
      contradiction
    · have i_lt_n : i < n-1 := by
        exact i_fin''
      have greater : A ⟨i + 1, i_fin⟩ > A ⟨i, i_fin'⟩ := by
        apply (Indices_props.left (i) i_lt_n).right
      have equal : (⟨i, i_fin'⟩ : Fin n) = ⟨j+1, j_fin⟩ := by
        exact Fin.mk.inj_iff.mpr h
      rw [equal] at greater
      assumption
    have greater' : (⟨i, i_fin'⟩ : Fin n) > ⟨j + 1, j_fin⟩ := by
      exact h
    have greater : A ⟨i, i_fin'⟩ > A ⟨j + 1, j_fin⟩ := by
      apply ih _ greater'
    have greater'' :  A ⟨i + 1, i_fin⟩ >  A ⟨i, i_fin'⟩ := by
      apply (Indices_props.left _ _).right
      exact i_fin''
    exact Nat.lt_trans (ih i_fin' h) greater''

  intro i
  intro non_zero_A
  rcases i with ⟨i, ih⟩
  induction' i with i ih
  · have no_between : (∀ m : ℕ, m > 0 ∧ m < (A (Fin.ofNat' n 0)) → P.Q m (m-1) ≠ 0) := by
      intro m
      intro h'
      rcases h' with ⟨a, b⟩
      by_contra c
      have m_non_zero : m ≠ 0 := by
        exact Nat.ne_zero_of_lt a
      have exists_in_A : ∃ i, m = A i := by
        apply no_missed_vals m ⟨m_non_zero, c⟩
      rcases exists_in_A with ⟨i, hi⟩
      rw [hi] at b
      have A_zero_lt_other : ∀ i : Fin n, i > 0 → A i > A 0 := by
        intro i' i_gt_zero
        apply all_i_non_zero_bigger_A i' 0 i_gt_zero
      rcases i with ⟨i, i_fin⟩
      rcases Nat.eq_zero_or_pos i with h | h'
      · have equal : (⟨i, i_fin⟩ : Fin n) = ⟨0, ih⟩ := by
          exact Fin.mk.inj_iff.mpr h
        have equal' : ⟨0, ih⟩ = (Fin.ofNat' n 0) := by
          exact rfl
        rw [equal, equal'] at b
        linarith [b]
      -- have A_i_gt_A_zero :
      have equal' : (Fin.ofNat' n 0) = ⟨0, ih⟩ := by
          exact rfl
      rw [equal'] at b
      have A_gt_zero : A ⟨i, i_fin⟩ > A ⟨0, ih⟩ := by
        exact all_i_non_zero_bigger_A ⟨i, i_fin⟩ ⟨0, ih⟩ h'
      linarith
    have based_on_previous_lambda : lambdaP (A ⟨0, ih⟩ - 1) = (∏i : (Fin (A ⟨0, ih⟩ - 1)),
      (P.Q (i) (i+1))/
      (P.Q (i+1) (i))) * lambdaP 0:= by
      have first_hypo : (∀ (i : ℕ), i ≠ 0 ∧ i < (A ⟨0, ih⟩) → P.Q i (i - 1) ≠ 0) := by
        -- use A ⟨0, ih⟩
        intro i
        rintro ⟨h, h'⟩
        have gt_zero : i > 0 := by
          exact Nat.zero_lt_of_ne_zero h
        apply no_between i ⟨gt_zero, h'⟩
      have second_hypo : (∀i, i < (A ⟨0, ih⟩) → P.Q i (i+1) ≠ 0) := by
        -- use A ⟨0, ih⟩
        intro i
        intro h
        apply pos_arrival i

      have A_sub_one_lt_A : (A ⟨0, ih⟩) - 1 < (A ⟨0, ih⟩) := by
        rcases Nat.eq_zero_or_pos (A ⟨0, ih⟩) with h' | h'
        · contradiction
        exact Nat.sub_one_lt_of_lt h'

        -- rintro ⟨h, h'⟩

      apply lemma2_3_3a' P lambdaP h'' (A ⟨0, ih⟩) ⟨first_hypo, second_hypo⟩ (A ⟨0, ih⟩ -1) A_sub_one_lt_A
    rcases Nat.eq_zero_or_pos (A ⟨0, ih⟩ - 1) with hypo | hypo
    · rw [hypo] at based_on_previous_lambda
      -- have equal : ∏ i : Fin 0, P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i = ∏ i ∈ Finset.range 0, P.Q (↑i) (↑i + 1) / P.Q (↑i + 1) ↑i := by
      --   exact rfl
      rw [hypo]
      rcases h'' with ⟨h₁'', h₁''', h₁''''⟩
      have hypo'' : A ⟨0, ih⟩ ≤ 1 := by
        exact Nat.le_of_sub_eq_zero hypo
      -- have hypo' : A ⟨0, ih⟩ = 0 ∨ A ⟨0, ih⟩ = 1 := by
      --   exact Nat.le_one_iff_eq_zero_or_eq_one.mp hypo''
      have hypo''' : A ⟨0, ih⟩ = 1 := by
        rcases (lt_trichotomy (A ⟨0, ih⟩) 1) with a | b | c
        · have d : A ⟨0, ih⟩ = 0 := by
            linarith
          contradiction
        · assumption
        linarith
      have hypo'''' : P.Q (A ⟨0, ih⟩) (A ⟨0, ih⟩-1) = 0 := by
        rcases (lt_trichotomy n 1) with a | b | c
        · linarith
        · have equal : mycast'(n,n_non_zero,Fin.last (n-1)) = ⟨0, ih⟩ := by
            have equal : mycast'(n,n_non_zero,Fin.last (n-1)) = mycast'(n,n_non_zero,Fin.last (0)) := by
              refine (Fin.cast_inj (n_sub_one_add_one_eq_n n n_non_zero)).mpr ?_
              rw [b]
              have one_sub_one_eq_zero : 1-(1 : ℕ)=0 := by
                exact rfl
              rw [one_sub_one_eq_zero]
              -- rw [sub_self 1]
              exact rfl
            have equal' : Fin.last (0) = 0 := by
              -- rw [b]
              -- have one_sub_one_eq_zero : 1-(1 : ℕ)=0 := by
              --   exact rfl
              -- rw [one_sub_one_eq_zero]
              exact rfl
            have equal''' : mycast'(n,n_non_zero,(Fin.last (0) : Fin (n-1+1))) = mycast'(n,n_non_zero,0) := by
              rw [equal']
              exact rfl
            have equal'''' : mycast'(n,n_non_zero,0) = 0 := by
              exact rfl
            rw [equal, equal''', equal'''']
            exact rfl
          rw [equal] at Indices_props
          apply Indices_props.right
        have zero_lt_n_sub_one : 0 < n -1 := by
          exact Nat.zero_lt_sub_of_lt c
        apply (Indices_props.left 0 zero_lt_n_sub_one).left non_zero_A
      rw [hypo, hypo'''] at hypo''''
      rw [hypo''''] at h₁'''
      ring_nf at h₁'''
      have two_options : P.Q 0 1 = 0 ∨ lambdaP 0 = 0 := by
        exact mul_eq_zero.mp (id (Eq.symm h₁'''))
      rcases two_options with h_ | h_
      · have pos_arrival' : P.Q 0 (0+1) ≠ 0 := by
          apply pos_arrival 0
        contradiction
      assumption
    have nice_rewrite : lambdaP (A ⟨0, ih⟩ - 1) = (P.Q (A ⟨0, ih⟩ - 2) (A ⟨0, ih⟩ - 1)) * lambdaP (A ⟨0, ih⟩ - 2) / ((P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩)) + (P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 2))) := by
      rcases h'' with ⟨h'', h''', h''''⟩
      have semi_nice_rewrite : ((P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩)) + (P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 2))) * lambdaP (A ⟨0, ih⟩ - 1) = (P.Q (A ⟨0, ih⟩ - 2) (A ⟨0, ih⟩ - 1)) * lambdaP (A ⟨0, ih⟩ - 2) := by
        rw [←add_zero ((P.Q (A ⟨0, ih⟩ - 2) (A ⟨0, ih⟩ - 1)) * lambdaP (A ⟨0, ih⟩ - 2))]
        rw [←zero_mul (lambdaP (A ⟨0, ih⟩))]
        rcases (lt_trichotomy n 1) with a | b | c
        · linarith
        · have equal : mycast'(n,n_non_zero,Fin.last (n-1)) = ⟨0, ih⟩ := by
            have equal : mycast'(n,n_non_zero,Fin.last (n-1)) = mycast'(n,n_non_zero,Fin.last (0)) := by
              refine (Fin.cast_inj (n_sub_one_add_one_eq_n n n_non_zero)).mpr ?_
              rw [b]
              have one_sub_one_eq_zero : 1-(1 : ℕ)=0 := by
                exact rfl
              rw [one_sub_one_eq_zero]
              -- rw [sub_self 1]
              exact rfl
            have equal' : Fin.last (0) = 0 := by
              -- rw [b]
              -- have one_sub_one_eq_zero : 1-(1 : ℕ)=0 := by
              --   exact rfl
              -- rw [one_sub_one_eq_zero]
              exact rfl
            have equal''' : mycast'(n,n_non_zero,(Fin.last (0) : Fin (n-1+1))) = mycast'(n,n_non_zero,0) := by
              rw [equal']
              exact rfl
            have equal'''' : mycast'(n,n_non_zero,0) = 0 := by
              exact rfl
            rw [equal, equal''', equal'''']
            exact rfl
          rw [equal] at Indices_props
          rw [←Indices_props.right]
          symm
          rw [mul_comm]
          nth_rewrite 2 [mul_comm]
          -- nth_rewrite 3 [mul_comm]
          have goal : lambdaP (A ⟨0, ih⟩ - 1 - 1) * P.Q (A ⟨0, ih⟩ - 1 - 1) (A ⟨0, ih⟩ - 1) +
                      lambdaP (A ⟨0, ih⟩ - 1 + 1) * P.Q (A ⟨0, ih⟩ - 1 + 1) (A ⟨0, ih⟩ - 1) =
                      (P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 1 + 1) + P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 1 - 1)) * lambdaP (A ⟨0, ih⟩ - 1) := by
            apply h'' (A ⟨0, ih⟩-1)
          have helper: A ⟨0, ih⟩ - 1 - 1 = A ⟨0, ih⟩ - 2 := by
            exact rfl
          rw [helper] at goal
          have helper': A ⟨0, ih⟩ - 1 + 1 = A ⟨0, ih⟩ := by
            exact n_sub_one_add_one_eq_n (A ⟨0, ih⟩) non_zero_A
          rw [helper'] at goal
          assumption
        have zero_lt_n_sub_one : 0 < n-1 := by
          exact Nat.zero_lt_sub_of_lt c
        rw [←(Indices_props.left 0 zero_lt_n_sub_one).left]
        symm
        nth_rewrite 1 [mul_comm]
        nth_rewrite 2 [mul_comm]
        have A_non_zero : A ⟨0, ih⟩ - 1 ≠ 0 := by
          exact Ne.symm (Nat.ne_of_lt hypo)
        have goal: lambdaP (A ⟨0, ih⟩ - 1 - 1) * P.Q (A ⟨0, ih⟩ - 1 - 1) (A ⟨0, ih⟩ - 1) +
            lambdaP (A ⟨0, ih⟩ - 1 + 1) * P.Q (A ⟨0, ih⟩ - 1 + 1) (A ⟨0, ih⟩ - 1) =
        (P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 1 + 1) + P.Q (A ⟨0, ih⟩ - 1) (A ⟨0, ih⟩ - 1 - 1)) * lambdaP (A ⟨0, ih⟩ - 1) := by
          apply h'' (A ⟨0, ih⟩-1) A_non_zero
        have helper: A ⟨0, ih⟩ - 1 - 1 = A ⟨0, ih⟩ - 2 := by
            exact rfl
        rw [helper] at goal
        have helper': A ⟨0, ih⟩ - 1 + 1 = A ⟨0, ih⟩ := by
          exact n_sub_one_add_one_eq_n (A ⟨0, ih⟩) non_zero_A
        rw [helper'] at goal
        assumption
        apply non_zero_A



          -- rw [add_comm]

            -- exact rfl

            -- refine Fin.eq_mk_iff_val_eq.mpr ?_
            -- refine Fin.val_eq_zero_iff.mpr ?_
            -- apply?

            -- rw [mycast']
            -- apply?
            -- rw [← equal']

            -- have equal'' : mycast'(n,n_non_zero,Fin.last (0)) = ⟨0, ih⟩ := by
            --   rw []



          -- apply Indices_props.right


        -- refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_ (A ⟨0, ih⟩)
        -- exact Nat.le_of_sub_eq_zero h
        -- apply?
      -- rw [equal]


        -- apply Finset.prod_range_zero
      -- rw [equal]
      -- apply Finset.prod_range_zero
    -- have prev_lambda : lambdaP (A ⟨0, ih⟩ - 1) = lambdaP (A ⟨0, ih⟩ - 1) := by



      -- apply i at A_zero_lt_other
      -- apply
      -- by_contra c
      -- apply no_missed_vals


  -- · have no_between : (¬∃m : ℕ, m ≠ 0 ∧ m < (A (Fin.ofNat' n 0)) → P.Q m (m-1) = 0) := by
  --     refine not_exists.mpr ?_
  --     intro x
  --     by_contra h'
  --     apply no_missed_vals
  --     use x

      -- apply not_exists.mpr ?_ at no_missed_vals


      -- push_neg at no_missed_vals
      -- push_neg
      -- intro m
      -- by_contra h''
      -- apply no_missed_vals


      -- push_neg
      -- intro m


      -- constructor
      -- ·







  -- simp at Indices_props

  -- sorry
--   intro i ⟨a, b⟩
--   induction' i with i ih
--   · have zero_in_rhs : (∀ x, x ∈ A → (x ∈ {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})) := by
      -- intro x h
      -- have hypo : x ∈ {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0} := by
      --   apply?
      -- rw [A']



      -- rw [←A']




  --  at a

  -- rintro h' at ⟨⟩
  -- by_contra
  sorry



-- Prove this later
lemma lemma2_3_3 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) (A : Finset {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})
  (Nonemptyset : A.Nonempty):
  ∀i : ℕ, i < A.max' Nonemptyset → lambdaP i = 0 := by
  sorry

  induction' n ∈ A with a b


--  Proof is mostly similar as in lemma2_3_1
lemma lemma2_3_4 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) (A : Finset {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})
  (Nonemptyset : A.Nonempty)
   : (∀i ≠ 0, P.Q i (i-1) ≠ 0) → (∃Λ, Λ > 0 → ∀ i, P.Q i (i+1) = Λ) →
  ∃ Λ, Λ > 0 → ∀ n, lambdaP (n + (A.max' Nonemptyset)) = (∏ i : (Fin n), Λ/(P.Q (i + (A.max' Nonemptyset) + 1) (i + (A.max' Nonemptyset)))) * (lambdaP (A.max' Nonemptyset)) := by
  let N := (A.max' Nonemptyset)

  intro non_zero ⟨Λ, constant_arrival⟩
  use Λ
  intro Λ_pos
  intro n

  induction' n using Nat.twoStepInduction with n ih ih₂
  have h' : (∏ i : (Fin 0), Λ / P.Q (↑i + (A.max' Nonemptyset) + 1) (↑i + (A.max' Nonemptyset))) = (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1 + (A.max' Nonemptyset)) (↑i + (A.max' Nonemptyset))) := by
    exact rfl

  rw [h']
  have h'' : (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1 + (A.max' Nonemptyset)) (↑i + (A.max' Nonemptyset)) = 1) := by
    apply Finset.prod_range_zero (fun i : ℕ => (Λ / P.Q (i + 1) i))
  rw[h'']
  ring_nf

  -- Start of ih
  rcases h with ⟨h, h', h''⟩
  have h''' : (∏ i : (Fin (1)), Λ / P.Q (↑i + (A.max' Nonemptyset) + 1) (↑i+ (A.max' Nonemptyset))) = (∏ i ∈ (Finset.range (1)), Λ / P.Q (↑i+ (A.max' Nonemptyset) + 1) (↑i+ (A.max' Nonemptyset))) := by
    exact rfl
  rw [h''']
  have one_sub_one_eq_zero : ((↑(A.max' Nonemptyset) + 1 - 1) : ℕ) = (↑(A.max' Nonemptyset) + 1 - 1) := by
    ring
  have non_zero_lt_max_plus_one : (A.max' Nonemptyset : ℕ) + (1 : ℕ) ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one ↑(A.max' Nonemptyset))

  have lambda_max_plus_one : lambdaP (↑(A.max' Nonemptyset) + 1) * P.Q ((↑((A.max' Nonemptyset)))+ 1) (A.max' Nonemptyset) = P.Q ((A.max' Nonemptyset)) ((A.max' Nonemptyset)+1) * lambdaP (A.max' Nonemptyset) := by
    sorry


  have h''''' : lambdaP (1 + (A.max' Nonemptyset)) = Λ/(P.Q ((A.max' Nonemptyset) + 1) (A.max' Nonemptyset))*(lambdaP (A.max' Nonemptyset)) := by
    rw [mul_comm, ←mul_div_assoc]
    symm
    apply div_eq_of_eq_mul (non_zero ((A.max' Nonemptyset) + 1) non_zero_lt_max_plus_one)
    symm
    rw [one_sub_one_eq_zero]
    rw [←constant_arrival Λ_pos (↑(A.max' Nonemptyset))]
    nth_rewrite 2 [mul_comm]
    exact h₁'
  have zero_add_one_eq_one : (0 + 1 : ℕ) = (1 :ℕ) := by
    ring
  rw [←zero_add_one_eq_one]
  have succ_range : (∏ i ∈ Finset.range (0+1), Λ / P.Q (↑i + 1) ↑i) = Λ / P.Q (0 + 1) 0 := by

    rw [Finset.prod_range_succ (fun i : ℕ => Λ / P.Q (↑i + (0 + 1)) ↑i) 0]
    rw [Finset.prod_range_zero]
    ring
  rw [succ_range]
  simp [h''''']




  sorry
