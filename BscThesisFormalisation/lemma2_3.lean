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
  lambdaP (i+2) = (((P.Q (i+1) i) + (P.Q (i+1) (i+2)))*(lambdaP (i+1)) - P.Q i (i+1)*lambdaP i)/P.Q (i+2) (i+1) := by
  rcases h with ⟨h, h', h''⟩
  have h₀: i + 1 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one i)
  have non_neq_P : 0 < P.Q (i + 2) (i + 1) := by
    apply P.departure_rate_greater_than_zero (i+1) h₀
  rw [eq_div_iff_mul_eq (ne_of_lt non_neq_P).symm]
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

lemma lemma2_3_1 (P : RateMatrix) (lambdaP : ℕ → ℝ) : (InvariantDistribution P lambdaP ∧ ∀i ≠ 0, P.Q i (i-1) ≠ 0) → (∃Λ, Λ > 0 → ∀ i, P.Q i (i+1) = Λ) →
  ∃ Λ, Λ > 0 → ∀ n, lambdaP n = (∏ i : (Fin n), Λ/(P.Q (i + 1) i)) * (lambdaP 0) := by
  rintro ⟨h₁, h₂⟩
  intro h
  rcases h with ⟨Λ, h⟩
  use Λ
  intro Λ_pos n
  induction' n using Nat.twoStepInduction with n ih ih₂
  have h' : (∏ i : (Fin 0), Λ / P.Q (↑i + 1) ↑i) = (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1) ↑i) := by
    exact rfl

  -- Case 0
  rw [h']
  have h'' : (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1) ↑i) = 1 := by
    apply Finset.prod_range_zero (fun i : ℕ => (Λ / P.Q (i + 1) i))
  rw[h'']
  ring

  -- Case 1
  rcases h₁ with ⟨h₁, h₁', h₁''⟩
  have h''' : (∏ i : (Fin (1)), Λ / P.Q (↑i + 1) ↑i) = (∏ i ∈ (Finset.range (1)), Λ / P.Q (↑i + 1) ↑i) := by
    exact rfl
  rw [h''']
  have one_sub_one_eq_zero : (1 : ℕ) - (1 : ℕ) = 0 := by
    exact rfl
  have h''''' : lambdaP 1 = Λ/(P.Q (0 + 1) 0)*(lambdaP 0) := by
    rw [mul_comm, ←mul_div_assoc]
    symm
    apply div_eq_of_eq_mul (h₂ 1 Nat.one_ne_zero)
    symm
    rw [one_sub_one_eq_zero]
    rw [←h Λ_pos 0]
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

  -- Start of ih proof
  rcases h₁ with ⟨h₁, h₁', h₁''⟩
  have val_gt_1_gt_0 : ∀(i : ℕ), i ≥ 1 → i ≠ 0 := by
    exact fun i a ↦ Nat.ne_zero_of_lt a -- From apply?
  have i_sub_one_gt :  ∀(i : ℕ), i ≥ 2 → i - 1 ≥ 1 := by
    exact fun i a ↦ Nat.le_sub_one_of_lt a
  rw [lemma2_3_help P lambdaP]
  symm
  rw [ih, ih₂]
  have copy1 : (∏ (i : Fin (n+2)), Λ / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+2)), Λ / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (Λ / P.Q (i + 1) i))

  have copy2 : (∏ (i : Fin (n+1)), Λ / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n+1)), Λ / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (Λ / P.Q (i + 1) i))

  have copy3 : (∏ (i : Fin (n)), Λ / P.Q (↑i + 1) ↑i) = (∏ (i ∈ Finset.range (n)), Λ / P.Q (↑i + 1) ↑i) := by
    symm
    apply Finset.prod_range (fun i : ℕ => (Λ / P.Q (i + 1) i))


  rw [copy1, copy2, copy3]
  rw [Finset.prod_range_succ]
  rw [Finset.prod_range_succ]

  have h₀: n + 1 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one n)
  have non_neq_P : 0 < P.Q (n + 2) (n + 1) := by
    apply P.departure_rate_greater_than_zero (n+1) h₀
  rw [eq_div_iff_mul_eq (ne_of_lt non_neq_P).symm]
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
  apply rewrite (∏ x ∈ Finset.range n, Λ / P.Q (x + 1) x)
  right
  have rewrite2 : Λ / P.Q (n + 1) n * (Λ / P.Q (n + 1 + 1) (n + 1) * (lambdaP 0 * P.Q (n + 2) (n + 1))) = (lambdaP 0) * (Λ / P.Q (n + 1) n * (Λ / P.Q (n + 1 + 1) (n + 1) * P.Q (n + 2) (n + 1))) := by
    ring

  have rewrite3 : Λ / P.Q (n + 1) n * (lambdaP 0 * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))) - lambdaP 0 * P.Q n (n + 1) = (lambdaP 0) * (Λ / P.Q (n + 1) n * (P.Q (n + 1) n + P.Q (n + 1) (n + 2))- P.Q n (n + 1)) := by
    ring
  rw [rewrite2, rewrite3]
  apply rewrite
  right
  have rewrite4 : n + 1 + 1 = n + 2 :=by
    ring
  rw [rewrite4]
  rw [h, h]
  rw [div_eq_mul_one_div]
  nth_rewrite 5 [←mul_one Λ]
  have rewrite5 : Λ * (1 / P.Q (n + 1) n) * (P.Q (n + 1) n + Λ) - Λ * 1 = Λ * ((1 / P.Q (n + 1) n) * (P.Q (n + 1) n + Λ) - 1) := by
    ring
  rw [rewrite5]
  rw [mul_assoc]
  rw [div_mul_cancel₀]
  apply rewrite Λ
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
  exact Λ_pos
  exact Λ_pos
  constructor
  exact h₁
  constructor
  exact h₁'
  exact h₁''

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
  ∀m', (n < m' ∧ m' ≤ k) → lambdaP m' = (∏i : (Fin (m'-n)), (P.Q (i + n) (i+n+1))/(P.Q (i+n+1) (i+n))) * lambdaP n := by
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
  -- by_contra
  -- apply?
  -- Start ih
  -- have mp_gt_n : m' + 1 > m → m' > n := by
  --   intro h
  --   linarith [h, m_gt_n]
  -- have k_add_one_sub_n_eq_k_sub_n_add_one : k - n = (k - n - 1) + 1 := by
  --   omega
  have fin_eq_range : (∏ i : (Fin (k - n)), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (k - n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    exact Eq.symm (Finset.prod_range fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))
  -- rw [fin_eq_range]
  -- rw [k_add_one_sub_n_eq_k_sub_n_add_one]

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
  -- · have mp_add_one_eq_n

  --   have hypo: m' > n := by
  --     apply antisymm_iff
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
    -- have k_geq_n_add_one : k ≥ n + 1 := by
    --   exact k_gt_n

    have k_geq_mp_add_one : k ≥ m' + 1 := by
      exact Nat.le_of_succ_le mp_le_k

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
    -- rcases inbetween_non_zero with ⟨arrival_non_zero, dep_non_zero⟩
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
      exact mp_le_k
    apply all_between_dep_nonzero (m' + 1)

    constructor
    · apply n_lt_mp_add_one
    apply hypo5
    exact h


    -- have
    -- have m_gt_n_and_m_lt_k_imp_mp_bt_n_k : n < m ∧ m < k → P.Q m (m - 1) ≠ 0 := by
    --   exact fun a ↦ dep_non_zero
    -- have m_gt_n_and_m_lt_k_imp_mp_bt_n_k : ∀l, (n < l ∧ l < k) → P.Q l (l - 1) ≠ 0 := by

    --   apply?

  --   intro m' mp_bt_n_k
  -- rcases m_bt_n_k with ⟨m_gt_n, m_lt_k⟩
    -- have mp_bt_n_k :

    -- apply?


    -- have hypo4 : ∀l : ℕ, (n < l ∧ l < k) → (P.Q (l-1) l ≠ 0) := by
    --   intro l
    --   have neq_if_not_eq : (P.Q (l-1) l ≠ 0) ↔ ¬(P.Q (l-1) l = 0) := by
    --     exact Eq.to_iff rfl
    --   intro ⟨a, b⟩
    --   rw [neq_if_not_eq]



      -- apply?
    -- have

    -- rw [div_self (dep_non_zero)]

    -- repeat rw [←mul_assoc]















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



  -- have n_le_mp : n ≤ m' := by
  --   refine Nat.le_of_lt_succ ?_
  --   simp
    -- apply lt_add_of_lt_of_pos
    -- refine Nat.lt_add_right 1 mp_gt_n
    -- linarith [mp_gt_n]

  have mp_add_one_sub_n_eq_mp_sub_n_add_one : m' + 1 - n = (m' - n) + 1 := by
    have h'' : m' > n  := by
      exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    have h' : n ≤ m' := by
      exact Nat.le_of_succ_le h''
    ring
    rw [Nat.add_sub_assoc h']
  rw [mp_add_one_sub_n_eq_mp_sub_n_add_one]
    -- refine  ?_
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
  have all_between_dep_nonzero : ∀ (m : ℕ), n < m ∧ m < k → P.Q (m) (m-1) ≠ 0 := by
    intro m h
    apply (inbetween_non_zero m h).right
  have hypo5 : m' + 1 < k := by
    exact mp_le_k
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

  -- have mp_add_one_gt_n :
  -- exact hypo5

  exact Nat.le_of_succ_le mp_le_k
  exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
  have mp_le_k : m' ≤ k := by
    exact Nat.le_of_add_right_le mp_le_k
  exact mp_le_k
  exact h



  -- have mp_add_one_le_k : m'  + 1 < k := by


  -- apply

  -- apply hypo5








    -- refine Nat.add_right_cancel_iff.mpr ?_
    -- refine Nat.sub_add_cancel ?_
    -- have hypo7 : m' > n := by
    --   exact Nat.succ_lt_succ_iff.mp mp_add_one_gt_n_add_one
    -- exact Nat.le_of_succ_le hypo7



  -- apply?

  -- simp

  -- ring


  -- rw [lambda_up_front]
  -- nth_rewrite 4 [mul_comm]
  -- rw [div_eq_mul_one_div]
  -- repeat rw [mul_assoc]
  -- apply rewrite
  -- right
  -- have prod_up_front : ((P.Q (m'' + 1) m'' + P.Q (m'' + 1) (m'' + 2)) *
  --     ∏ i : Fin (k-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n) -
  --     P.Q m'' (m'' + 1) *
  --     ∏ i : Fin (k - n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) *
  --     (1 / P.Q (m'' + 2) (m'' + 1)) =
  --     ((∏ i : Fin (k-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) *
  --     (((P.Q (m'' + 1) m'' + P.Q (m'' + 1) (m'' + 2)) - P.Q m'' (m'' + 1)) *
  --     (1 / P.Q (m'' + 2) (m'' + 1)))) := by
  --     repeat rw [←mul_assoc]
  --     nth_rewrite 2 [mul_comm]
  --     nth_rewrite 3 [mul_comm]
  --     repeat rw [mul_assoc]
  --     rw [←mul_sub]
  --     repeat rw [mul_assoc]
  -- rw [prod_up_front]
  -- nth_rewrite 2 [←mul_one (∏ i : Fin (k-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n))]
  -- apply rewrite (∏ i : Fin (k-n), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n))
  -- right











    -- repeat rw [mul_assoc]
    -- rw [mul_assoc]





  -- rw [Finset.prod_range_succ (fun i ↦ P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n)) (k'-n + 1)]




  -- rw [ih]
    -- apply lt_trans
  -- apply ih (linarith [m_gt_n])


    -- have zero_sub_n_eq_zero : 0-n = 0 := by
    --   exact Nat.zero_sub n
    -- have h'' : (∏ i : (Fin (0-n)), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) = (∏ i ∈ Finset.range (0), P.Q (↑i + n) (↑i + n + 1) / P.Q (↑i + n + 1) (↑i + n)) := by
    --   rw [zero_sub_n_eq_zero]
    --   -- simp
    --   exact rfl
    -- rw [h'']
    -- have h''' : (∏ i ∈ Finset.range 0, P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n)) = 1 := by
    --   apply Finset.prod_range_zero (fun i : ℕ => P.Q (i + n) (i + n + 1) / P.Q (i + n + 1) (i + n))
    -- rw [h''']
    -- have h'''' : k - n = 0 := by
    --   apply?
    -- ring_nf!




lemma lemma2_3_3 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) (A : Finset {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})
  (Nonemptyset : A.Nonempty) :
  ∀i : ℕ, i < A.max' Nonemptyset → lambdaP i = 0 := by
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
