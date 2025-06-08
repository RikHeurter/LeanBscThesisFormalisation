import Mathlib
import BscThesisFormalisation.definitions
import BscThesisFormalisation.identities


example (n : ℕ) : (∃k, 2 * k = n ) ∨  (¬∃k, 2 * k = n) := by
  exact Classical.em (∃ k, 2 * k = n)


lemma lemma2_3_3 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h₀ :InvariantDistribution P lambdaP) (n : ℕ) [NeZero n] (n_non_zero: n ≠ 0) (A : Fin n → ℕ)
  (Indices_props : (∀i : ℕ, (h : i < n-1) → (A ⟨i, (helper_lema i h)⟩) < (A ⟨i+1, helper_lema' i h⟩)) ∧
  (∀ i : ℕ, (h: i < n) → A ⟨i, h⟩ ≠ 0 → P.Q (A ⟨i, h⟩) (A ⟨i, h⟩-1) = 0)):
  (∀i : ℕ, P.Q i (i+1) ≠ 0) → (∀m : ℕ, m ≠ 0 ∧ P.Q (m) (m-1) = 0 → ∃i : Fin (n), m = A i) → ∀ i : Fin (A  (↑(n - 1))), lambdaP i = 0 := by


  have h₁ : (∀i : ℕ, P.Q i (i+1) ≠ 0) → (∀m : ℕ, m ≠ 0 ∧ P.Q (m) (m-1) = 0 → ∃i : Fin (n), m = A i) → ∀ i : Fin n, A i ≠ 0 → lambdaP ((A i)-1) = 0 := by
    apply lemma2_3_3b P lambdaP h₀ n n_non_zero A Indices_props
  intro pos_arrival
  intro no_missed_vals
  have h₂ : ∀ i : Fin (n), (h:(1 : ℕ) ≤ ↑i) → lambdaP (A ((Fin.castSucc i).subNat 1 h)) = 0 := by
    exact fun i h ↦
      lemma2_3_3d P lambdaP h₀ n n_non_zero A Indices_props pos_arrival no_missed_vals i h
  have h₃ : (∀i : ℕ, P.Q i (i+1) ≠ 0) → (∀m : ℕ, m ≠ 0 ∧ P.Q (m) (m-1) = 0 → ∃i : Fin (n), m = A i) → (∃i, A i ≠ 0) → lambdaP 0 = 0 := by
    intro h h' ih
    apply lemma2_3_3c P lambdaP h₀ n n_non_zero A Indices_props pos_arrival no_missed_vals ih
  intro ⟨i, ifin⟩
  rcases (lt_trichotomy i 0) with a | b | c
  · linarith
  · simp
    rw [b]
    rw [b] at ifin
    have non_zero_A : A (↑(n - 1)) ≠ 0 := by
      exact Nat.ne_zero_of_lt ifin
    have helper : ∃i, A i ≠ 0 := by
      use (↑(n - 1))
    apply h₃ pos_arrival no_missed_vals helper
  rcases (Classical.em (∃j, A j = i)) with h| h
  · rcases h with ⟨⟨j, jfin⟩, jelp⟩
    have j_add_one_ge_one: j + 1 ≥ 1 := by
      have j_ge_zero: j ≥ 0 := by
        exact Nat.zero_le j
      exact Nat.le_add_of_sub_le j_ge_zero
    have j_add_one_lt_n : j + 1 < n := by
      rcases (lt_trichotomy (j+1) n) with d | e | f
      · exact d
      · have n_sub_one_eq_j : n -1 = j:= by
          exact Eq.symm (Nat.eq_sub_of_add_eq e)
        -- rw [n_sub_one_eq_j] at ifin
        have casted_version : (↑(n -1) : Fin n) = ⟨j, jfin⟩ := by
          refine Fin.eq_mk_iff_val_eq.mpr ?_
          rw [n_sub_one_eq_j]
          exact Fin.val_cast_of_lt jfin
        rw [casted_version] at ifin
        rw [←jelp] at ifin
        linarith
      have n_sub_one_eq_j : n -1 < j:= by
        refine Nat.sub_one_lt_of_le ?_ ?_
        exact Nat.zero_lt_of_ne_zero n_non_zero
        exact Nat.le_of_lt_succ f
      have j_ge_n : j ≥ n := by
        exact Nat.le_of_lt_succ f
      linarith
    -- have j_lt_n_sub_one : j < n - 1 := by
    --   exact Nat.lt_sub_of_add_lt j_add_one_lt_n
    -- have small_helper : 1 ≤ ↑(⟨j, j_lt_n_sub_one⟩ : Fin (n-1)).castSucc := by
    --   simp
    --   apply?
    have almost_there : lambdaP (A (Fin.subNat 1 (⟨j+1, j_add_one_lt_n⟩ : Fin (n)).castSucc j_add_one_ge_one)) = 0 := by
      exact h₂ ⟨j + 1, j_add_one_lt_n⟩ j_add_one_ge_one
    simp at almost_there
    rw [jelp] at almost_there
    simp
    exact almost_there
  push_neg at h
  have i_lt_A_neq_zero : ∃k : Fin n, A (k-1) < i ∧ i < A k := by
    intro k


  -- ·





  sorry







    --   exact Fin.mk.inj_iff.mpr (id (Eq.symm h''))
    -- rw [rewrite] at b
    -- linarith

    -- rw [hi] at a
      -- apply all_i_non_zero_bigger_A ⟨i, i_fin⟩ ⟨1, one_lt_n⟩ h'




    -- Now redo proof of lemma2_3_3c!!!!!

    -- rw [h₀]
    -- have helper : ∃i, A i ≠ 0 := by
    --   use ⟨i, ifin⟩
    --   rw [ifin_eq_one_fin]
    --   exact A_appl_one_neq_zero





      -- rw?
      -- apply?


      -- ext
      -- rw [←Fin.mk_one]


    -- have helper : Fin.ofNat' n 1 = ⟨1, one_lt_n⟩ := by
    --   refine Fin.eq_mk_iff_val_eq.mpr ?_
    --   refine Eq.symm (Nat.le_antisymm ?_ ?_)
    --   · refine Nat.one_le_iff_ne_zero.mpr ?_
    --     refine Fin.val_ne_zero_iff.mpr ?_
    --     have helper: (Fin.ofNat' n 1).val = 1 := by
    --       apply?


    -- have eq_zero : (⟨1, one_lt_n⟩ : Fin n) - 1 = 0 := by
      -- refine Eq.symm (Fin.ext ?_)
      -- refine Fin.val_eq_of_eq ?_
      -- refine Eq.symm (sub_eq_zero_of_eq ?_)
      -- refine Fin.le_antisymm ?_ ?_
      -- · refine Fin.mk_le_of_le_val ?_
      --   apply?
    -- have one_sub_one_lt_n : 1-1 < n:= by
    --   exact zero_lt_n

    -- have one_lt_n_add_one : 1 < n + n := by
    --   exact Nat.lt_add_right n one_lt_n

      -- exact Nat.lt_add_of_pos_left zero_lt_n
    -- have n_ge_two : n ≥ 2 := by
    --   exact one_lt_n

    -- have i_sub_one_eq_zero : (⟨i, ifin⟩ - 1 : Fin n) = ⟨0, zero_lt_n⟩ := calc
    --   (⟨i, ifin⟩ - 1 : Fin n) = (⟨1, one_lt_n⟩ - 1 : Fin n) := by
    --     rw [ifin_eq_one_fin]
    --   _ = (⟨1, one_lt_n_add_one⟩ : Fin (n + n)).subNat 1 (by decide) := by
    --     apply?


      -- _ = (1 : (Fin n)) - (1 : (Fin n)) := by
      --   apply?
      --   have helper: (1 : (Fin n)) = ⟨1, one_lt_n⟩ := by
      --     -- refine Fin.eq_mk_iff_val_eq.mpr ?_
      --     apply?
      --   rw [←helper]
      -- _ = (0 : (Fin n)) := by
      --   apply?
        -- refine Fin.eq_mk_iff_val_eq.mpr ?_
        -- apply?
        -- apply?
      -- _ = (⟨1-1, one_sub_one_lt_n⟩ : Fin n) := by
      --   refine Fin.eq_mk_iff_val_eq.mpr ?_
      --   apply?
      -- have also :
      -- refine Fin.eq_mk_iff_val_eq.mpr ?_
      -- refine Fin.val_eq_zero_iff.mpr ?_
      -- apply?



      -- apply?

    -- linarith

  -- constructor
  -- · induction' i with i ih
  --   · contradiction
  --   have i_lt_n : i < n := by
  --     exact Nat.lt_of_succ_lt ifin



  -- sorry


-- Prove this later
-- lemma lemma2_3_3 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) (A : Finset {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})
--   (Nonemptyset : A.Nonempty):
--   ∀i : ℕ, i < A.max' Nonemptyset → lambdaP i = 0 := by
--   sorry

--   induction' n ∈ A with a b


-- --  Proof is mostly similar as in lemma2_3_1
-- lemma lemma2_3_4 (P : RateMatrix) (lambdaP : ℕ → ℝ) (h :InvariantDistribution P lambdaP) (A : Finset {n : ℕ // n ≠ 0 ∧ P.Q n (n-1) = 0})
--   (Nonemptyset : A.Nonempty)
--    : (∀i ≠ 0, P.Q i (i-1) ≠ 0) → (∃Λ, Λ > 0 → ∀ i, P.Q i (i+1) = Λ) →
--   ∃ Λ, Λ > 0 → ∀ n, lambdaP (n + (A.max' Nonemptyset)) = (∏ i : (Fin n), Λ/(P.Q (i + (A.max' Nonemptyset) + 1) (i + (A.max' Nonemptyset)))) * (lambdaP (A.max' Nonemptyset)) := by
--   let N := (A.max' Nonemptyset)

--   intro non_zero ⟨Λ, constant_arrival⟩
--   use Λ
--   intro Λ_pos
--   intro n

--   induction' n using Nat.twoStepInduction with n ih ih₂
--   have h' : (∏ i : (Fin 0), Λ / P.Q (↑i + (A.max' Nonemptyset) + 1) (↑i + (A.max' Nonemptyset))) = (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1 + (A.max' Nonemptyset)) (↑i + (A.max' Nonemptyset))) := by
--     exact rfl

--   rw [h']
--   have h'' : (∏ i : (Finset.range (0)), Λ / P.Q (↑i + 1 + (A.max' Nonemptyset)) (↑i + (A.max' Nonemptyset)) = 1) := by
--     apply Finset.prod_range_zero (fun i : ℕ => (Λ / P.Q (i + 1) i))
--   rw[h'']
--   ring_nf

--   -- Start of ih
--   rcases h with ⟨h, h', h''⟩
--   have h''' : (∏ i : (Fin (1)), Λ / P.Q (↑i + (A.max' Nonemptyset) + 1) (↑i+ (A.max' Nonemptyset))) = (∏ i ∈ (Finset.range (1)), Λ / P.Q (↑i+ (A.max' Nonemptyset) + 1) (↑i+ (A.max' Nonemptyset))) := by
--     exact rfl
--   rw [h''']
--   have one_sub_one_eq_zero : ((↑(A.max' Nonemptyset) + 1 - 1) : ℕ) = (↑(A.max' Nonemptyset) + 1 - 1) := by
--     ring
--   have non_zero_lt_max_plus_one : (A.max' Nonemptyset : ℕ) + (1 : ℕ) ≠ 0 := by
--     exact Ne.symm (Nat.zero_ne_add_one ↑(A.max' Nonemptyset))

--   have lambda_max_plus_one : lambdaP (↑(A.max' Nonemptyset) + 1) * P.Q ((↑((A.max' Nonemptyset)))+ 1) (A.max' Nonemptyset) = P.Q ((A.max' Nonemptyset)) ((A.max' Nonemptyset)+1) * lambdaP (A.max' Nonemptyset) := by
--     sorry


--   have h''''' : lambdaP (1 + (A.max' Nonemptyset)) = Λ/(P.Q ((A.max' Nonemptyset) + 1) (A.max' Nonemptyset))*(lambdaP (A.max' Nonemptyset)) := by
--     rw [mul_comm, ←mul_div_assoc]
--     symm
--     apply div_eq_of_eq_mul (non_zero ((A.max' Nonemptyset) + 1) non_zero_lt_max_plus_one)
--     symm
--     rw [one_sub_one_eq_zero]
--     rw [←constant_arrival Λ_pos (↑(A.max' Nonemptyset))]
--     nth_rewrite 2 [mul_comm]
--     exact h₁'
--   have zero_add_one_eq_one : (0 + 1 : ℕ) = (1 :ℕ) := by
--     ring
--   rw [←zero_add_one_eq_one]
--   have succ_range : (∏ i ∈ Finset.range (0+1), Λ / P.Q (↑i + 1) ↑i) = Λ / P.Q (0 + 1) 0 := by

--     rw [Finset.prod_range_succ (fun i : ℕ => Λ / P.Q (↑i + (0 + 1)) ↑i) 0]
--     rw [Finset.prod_range_zero]
--     ring
--   rw [succ_range]
--   simp [h''''']




--   sorry
