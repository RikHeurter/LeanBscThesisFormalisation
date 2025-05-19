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

  rw [h']
  have h'' : (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1) ↑i) = 1 := by
    apply Finset.prod_range_zero (fun i : ℕ => (Λ / P.Q (i + 1) i))
  rw[h'']
  ring

  -- Start of ih proof
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



lemma lemma2_3_2 (P : RateMatrix) (lambdaP : ℕ → ℝ) : InvariantDistribution P lambdaP ∧ ∀i ≠ 0, P.Q i (i-1) ≠ 0 ∧ ∃Λ, ∀ i, P.Q i (i+1) = Λ →
  lambdaP 0 = 1/(∑'n, (∏ i : (Fin (n-1)), Λ/(P.Q (i + 1) i))) := by sorry
