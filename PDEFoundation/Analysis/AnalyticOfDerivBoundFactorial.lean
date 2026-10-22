module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PDE

open scoped Nat

/-- The elementary growth estimate used to turn `m^m` derivative bounds into
factorial bounds. -/
theorem natCast_pow_self_le_exp_one_pow_mul_factorial (m : ℕ) :
    (m : ℝ) ^ m ≤ (Real.exp 1) ^ m * (m ! : ℝ) := by
  by_cases hm : m = 0
  · subst m
    norm_num
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hpi : (1 : ℝ) ≤ Real.pi := by
    linarith [Real.one_le_pi_div_two]
  have hrad : (1 : ℝ) ≤ 2 * Real.pi * m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hmone)]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (2 * Real.pi * m) := Real.sqrt_le_sqrt hrad
  have hbase : 0 ≤ ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hstir : ((m : ℝ) / Real.exp 1) ^ m ≤ (m ! : ℝ) :=
    (le_mul_of_one_le_left hbase hsqrt).trans (Stirling.le_factorial_stirling m)
  have hexp : 0 ≤ (Real.exp 1) ^ m := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstir hexp
  have hne : (Real.exp 1) ^ m ≠ 0 := pow_ne_zero _ (Real.exp_ne_zero 1)
  rw [div_pow] at hmul
  have hcancel : (Real.exp 1) ^ m * ((m : ℝ) ^ m / (Real.exp 1) ^ m) =
      (m : ℝ) ^ m := by
    field_simp
  rw [hcancel] at hmul
  exact hmul

/-- A derivative bound of the form `(a m)^m` becomes a geometric Taylor
coefficient bound after division by `m!`. -/
theorem scaled_pow_div_factorial_le_exp_pow (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (a * m) ^ m / (m ! : ℝ) ≤ (Real.exp 1 * a) ^ m := by
  have hfac : (0 : ℝ) < (m ! : ℝ) := by positivity
  apply (div_le_iff₀ hfac).2
  calc
    (a * m) ^ m = a ^ m * (m : ℝ) ^ m := mul_pow a (m : ℝ) m
    _ ≤ a ^ m * ((Real.exp 1) ^ m * (m ! : ℝ)) :=
      mul_le_mul_of_nonneg_left (natCast_pow_self_le_exp_one_pow_mul_factorial m)
        (pow_nonneg ha m)
    _ = (Real.exp 1 * a) ^ m * (m ! : ℝ) := by rw [mul_pow]; ring

/-- The same conversion with a nonnegative prefactor and a line-direction
factor. -/
theorem scaled_pow_line_div_factorial_le_geometric (m : ℕ)
    {M K s : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hs : 0 ≤ s) :
    M * (K * m) ^ m * s ^ m / (m ! : ℝ) ≤
      M * (Real.exp 1 * K * s) ^ m := by
  calc
    M * (K * m) ^ m * s ^ m / (m ! : ℝ) =
        M * ((K * m) ^ m / (m ! : ℝ)) * s ^ m := by ring
    _ ≤ M * (Real.exp 1 * K) ^ m * s ^ m := by
      gcongr
      exact scaled_pow_div_factorial_le_exp_pow m hK
    _ = M * (Real.exp 1 * K * s) ^ m := by rw [mul_pow]; ring

end PDE
