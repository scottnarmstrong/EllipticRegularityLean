module

public import PDEFoundation.Analysis.TwoFourInterpolationArithmetic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace PDE

/-- An entire power family for a real scalar, with the zero scalar represented
by its zero sign coefficient. -/
noncomputable def analyticPowerFamilyTerm
    (x a b : ℝ) (z : ℂ) : ℂ :=
  (((SignType.sign x : ℝ) : ℂ) *
    Complex.exp ((Real.log |x| : ℂ) * ((b : ℂ) + (a : ℂ) * z)))

theorem analyticPowerFamilyTerm_differentiable (x a b : ℝ) :
    Differentiable ℂ (analyticPowerFamilyTerm x a b) := by
  apply Differentiable.const_mul
  exact Complex.differentiable_exp.comp
    ((differentiable_const (b : ℂ)).add (differentiable_id.const_mul (a : ℂ)) |>.const_mul
      (Real.log |x| : ℂ))

/-- The norm of the power family is the corresponding real power whenever the
real exponent is positive. -/
theorem norm_analyticPowerFamilyTerm
    (x a b : ℝ) (z : ℂ) (ht : 0 < b + a * z.re) :
    ‖analyticPowerFamilyTerm x a b z‖ = |x| ^ (b + a * z.re) := by
  by_cases hx : x = 0
  · subst x
    simp [analyticPowerFamilyTerm, Real.zero_rpow ht.ne']
  · have hsign : ‖(((SignType.sign x : ℝ) : ℂ))‖ = 1 := by
      rcases lt_or_gt_of_ne hx with hxNeg | hxPos
      · rw [sign_neg hxNeg]
        norm_num
      · rw [sign_pos hxPos]
        norm_num
    rw [analyticPowerFamilyTerm, Complex.norm_mul, hsign, one_mul, Complex.norm_exp]
    rw [Real.rpow_def_of_pos (abs_pos.mpr hx)]
    congr 1
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]

/-- At a real parameter where the affine exponent is one, the power family
recovers the original real scalar. -/
theorem analyticPowerFamilyTerm_eq_real
    (x a b : ℝ) (z : ℂ) (hzIm : z.im = 0) (ht : b + a * z.re = 1) :
    analyticPowerFamilyTerm x a b z = (x : ℂ) := by
  have hexponent : (b : ℂ) + (a : ℂ) * z = 1 := by
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.one_re] using ht
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, zero_add, Complex.one_im, hzIm, mul_zero]
  by_cases hx : x = 0
  · subst x
    simp [analyticPowerFamilyTerm]
  · rw [analyticPowerFamilyTerm, hexponent, mul_one, ← Complex.ofReal_exp,
      Real.exp_log (abs_pos.mpr hx)]
    exact_mod_cast sign_mul_abs x

/-- At the left edge, the input power family has squared norm `|x|^p`. -/
theorem norm_analyticPowerFamilyTerm_input_zero
    (x p : ℝ) (hp : 2 ≤ p) (z : ℂ) (hz : z.re = 0) :
    ‖analyticPowerFamilyTerm x (-(p / 4)) (p / 2) z‖ ^ 2 = |x| ^ p := by
  rw [norm_analyticPowerFamilyTerm x (-(p / 4)) (p / 2) z (by rw [hz]; linarith), hz]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

/-- At the right edge, the input power family has fourth power norm `|x|^p`. -/
theorem norm_analyticPowerFamilyTerm_input_one
    (x p : ℝ) (hp : 2 ≤ p) (z : ℂ) (hz : z.re = 1) :
    ‖analyticPowerFamilyTerm x (-(p / 4)) (p / 2) z‖ ^ 4 = |x| ^ p := by
  rw [norm_analyticPowerFamilyTerm x (-(p / 4)) (p / 2) z (by rw [hz]; linarith), hz]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

/-- At the interpolation parameter, the input power family recovers `x`. -/
theorem analyticPowerFamilyTerm_input_interpolation
    (x p : ℝ) (hp : 2 ≤ p) :
    analyticPowerFamilyTerm x (-(p / 4)) (p / 2) (2 - 4 / p : ℝ) = (x : ℂ) := by
  apply analyticPowerFamilyTerm_eq_real
  · simp
  · have hpZero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
    simp only [Complex.ofReal_re]
    field_simp [hpZero]
    ring

/-- At the left edge, the dual power family has squared norm `|x|^(p/(p-1))`. -/
theorem norm_analyticPowerFamilyTerm_dual_zero
    (x p : ℝ) (hp : 2 ≤ p) (z : ℂ) (hz : z.re = 0) :
    ‖analyticPowerFamilyTerm x ((p / (p - 1)) / 4) ((p / (p - 1)) / 2) z‖ ^ 2 =
      |x| ^ (p / (p - 1)) := by
  have hpSubPos : 0 < p - 1 := by linarith
  have hpDualPos : 0 < p / (p - 1) := div_pos (lt_of_lt_of_le (by norm_num) hp) hpSubPos
  rw [norm_analyticPowerFamilyTerm x ((p / (p - 1)) / 4) ((p / (p - 1)) / 2) z
    (by rw [hz]; linarith), hz]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
  congr 1
  ring

/-- At the right edge, the dual power family has `4/3`-power norm
`|x|^(p/(p-1))`. -/
theorem norm_analyticPowerFamilyTerm_dual_one
    (x p : ℝ) (hp : 2 ≤ p) (z : ℂ) (hz : z.re = 1) :
    ‖analyticPowerFamilyTerm x ((p / (p - 1)) / 4) ((p / (p - 1)) / 2) z‖ ^
        (4 / 3 : ℝ) = |x| ^ (p / (p - 1)) := by
  have hpSubPos : 0 < p - 1 := by linarith
  have hpDualPos : 0 < p / (p - 1) := div_pos (lt_of_lt_of_le (by norm_num) hp) hpSubPos
  rw [norm_analyticPowerFamilyTerm x ((p / (p - 1)) / 4) ((p / (p - 1)) / 2) z
    (by rw [hz]; linarith), hz]
  rw [← Real.rpow_mul (abs_nonneg x)]
  congr 1
  field_simp [hpSubPos.ne']
  ring

/-- At the interpolation parameter, the dual power family recovers `x`. -/
theorem analyticPowerFamilyTerm_dual_interpolation
    (x p : ℝ) (hp : 2 ≤ p) :
    analyticPowerFamilyTerm x ((p / (p - 1)) / 4) ((p / (p - 1)) / 2)
        (2 - 4 / p : ℝ) = (x : ℂ) := by
  apply analyticPowerFamilyTerm_eq_real
  · simp
  · have hpZero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
    have hpSubZero : p - 1 ≠ 0 := by linarith
    simp only [Complex.ofReal_re]
    field_simp [hpZero, hpSubZero]
    ring

end PDE
