module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Arithmetic for interpolation between exponents two and four

These scalar identities give the interpolation weight and the moduli of
positive-base analytic coefficients. No operator interpolation estimate is
assumed or asserted here.
-/

@[expose] public section

namespace PDE

/-- The interpolation weight lies in the closed unit interval. -/
theorem two_four_interpolation_weight_mem_Icc {p : ℝ}
    (hp : 2 ≤ p) (hpFour : p ≤ 4) :
    2 - 4 / p ∈ Set.Icc (0 : ℝ) 1 := by
  have hpPos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hpPos).mpr
    linarith only [hp]
  · have hratio : 1 ≤ 4 / p := by
      apply (le_div_iff₀ hpPos).mpr
      simpa only [one_mul] using hpFour
    linarith only [hratio]

/-- Reciprocal primal exponents interpolate with this weight. -/
theorem two_four_interpolation_reciprocal (p : ℝ) :
    (1 - (2 - 4 / p)) / 2 + (2 - 4 / p) / 4 = 1 / p := by
  ring

/-- Reciprocal dual exponents interpolate with the same weight. -/
theorem two_four_interpolation_dual_reciprocal (p : ℝ) :
    (1 - (2 - 4 / p)) / 2 + 3 * (2 - 4 / p) / 4 = 1 - 1 / p := by
  ring

/-- The primal analytic exponent is one at the interpolation point. -/
theorem two_four_interpolation_primal_exponent {p : ℝ} (hp : p ≠ 0) :
    p * ((1 - (2 - 4 / p)) / 2 + (2 - 4 / p) / 4) = 1 := by
  rw [two_four_interpolation_reciprocal]
  exact mul_one_div_cancel hp

/-- Positive real complex powers have the modulus prescribed by the real
interpolated reciprocal exponent. -/
theorem norm_two_four_interpolation_coefficient
    {b : ℝ} (hb : 0 < b) (p : ℝ) (z : ℂ) :
    ‖(b : ℂ) ^ ((p : ℂ) *
      ((1 - z) * ((1 / 2 : ℝ) : ℂ) + z * ((1 / 4 : ℝ) : ℂ)))‖ =
      b ^ (p * ((1 - z.re) / 2 + z.re / 4)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb]
  congr 1
  simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

end PDE
