import Mathlib

example (a b c d: ℝ) (ha : a ≠ 0) (hb: b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) : a/b = c/d → ∃ e, a = e*c ∧ b = e*d := by
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


  -- intro ⟨h₀, h₁⟩
  -- have h''' : a*d = c*b := by

  --   apply (div_eq_div_iff).mp h h' at h
  -- apply?
