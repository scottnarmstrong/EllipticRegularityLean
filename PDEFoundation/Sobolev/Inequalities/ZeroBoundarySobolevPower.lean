module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolev

/-!
# Integral-power critical Sobolev inequality for `H¹₀`

The extended-real critical Sobolev estimate is converted here to the real
integral-power form used by De Giorgi iteration.  Both exponent identities
and finiteness of the two norms are proved explicitly, so this module does
not hide a real-valued `∞ - ∞` conversion behind a coercion.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- The reciprocal critical-power identity in the form used to turn an
`L^(2d/(d-2))` norm into a squared energy estimate. -/
theorem two_div_sobolevConjugate_two
    {d : ℕ} (hd : 3 ≤ d) :
    2 / sobolevConjugate d 2 =
      ((d : ℝ) - 2) / (d : ℝ) := by
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast (by omega : 0 < d)
  have hd_gt_two : (2 : ℝ) < d := by
    exact_mod_cast (by omega : 2 < d)
  have hd_sub_pos : (0 : ℝ) < (d : ℝ) - 2 := by
    linarith
  unfold sobolevConjugate
  field_simp [hd_pos.ne', hd_sub_pos.ne']

/-- Critical zero-boundary Sobolev in the real integral-power form.  The
constant is dimension-only, and the Euclidean gradient energy is exact. -/
theorem setIntegral_abs_rpow_sobolevConjugate_two_rpow_two_div_le
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (u : H10Function U) :
    (∫ x in U, |u.toFun x| ^ (sobolevConjugate d 2) ∂volume) ^
        (2 / sobolevConjugate d 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ∫ x in U, vecNormSq (u.grad x) ∂volume := by
  let q : ℝ := sobolevConjugate d 2
  have hq : 0 < q := by
    dsimp [q]
    apply sobolevConjugate_pos (by norm_num)
    exact_mod_cast hd
  have hGradMem :
      MemLp (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn U) :=
    u.gradMemL2.memLp_vecEuclideanNorm
  have hGradNorm_ne_top : euclideanFieldELpNormOn U 2 u.grad ≠ ∞ := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn] using
      hGradMem.eLpNorm_ne_top
  have hSob :=
    eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd u
  have hValueMem : MemLp u.toFun (ENNReal.ofReal q) (volumeOn U) := by
    apply lt_of_le_of_lt (by
      simpa only [eLpNormOn, q, volumeOn] using hSob)
    exact lt_top_iff_ne_top.mpr <|
      ENNReal.mul_ne_top ENNReal.coe_ne_top hGradNorm_ne_top
  have hSobReal :
      (eLpNormOn U (ENNReal.ofReal q) u.toFun).toReal ≤
        (zeroBoundarySobolevConstantTwo d : ℝ) *
          (euclideanFieldELpNormOn U 2 u.grad).toReal := by
    have hRight_ne_top :
        (zeroBoundarySobolevConstantTwo d : ℝ≥0∞) *
          euclideanFieldELpNormOn U 2 u.grad ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hGradNorm_ne_top
    have h := ENNReal.toReal_mono hRight_ne_top (by
      simpa only [q] using hSob)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
  have hValue :
      (eLpNormOn U (ENNReal.ofReal q) u.toFun).toReal ^ q =
        ∫ x in U, |u.toFun x| ^ q ∂volume := by
    simpa only [eLpNormOn, volumeOn, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hq hValueMem
  have hValuePower :
      (∫ x in U, |u.toFun x| ^ q ∂volume) ^ (2 / q) =
        (eLpNormOn U (ENNReal.ofReal q) u.toFun).toReal ^ 2 := by
    rw [← hValue, ← Real.rpow_mul ENNReal.toReal_nonneg]
    have hq_ne : q ≠ 0 := hq.ne'
    rw [show q * (2 / q) = (2 : ℝ) by field_simp [hq_ne]]
    exact Real.rpow_natCast _ 2
  have hGradient :
      (euclideanFieldELpNormOn U 2 u.grad).toReal ^ 2 =
        ∫ x in U, vecNormSq (u.grad x) ∂volume := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn,
      vecEuclideanNorm_sq] using
      toReal_eLpNorm_two_sq_eq_integral_sq hGradMem
  have hSobSq :
      (eLpNormOn U (ENNReal.ofReal q) u.toFun).toReal ^ 2 ≤
        ((zeroBoundarySobolevConstantTwo d : ℝ) *
          (euclideanFieldELpNormOn U 2 u.grad).toReal) ^ 2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)).2 hSobReal
  calc
    (∫ x in U, |u.toFun x| ^ (sobolevConjugate d 2) ∂volume) ^
        (2 / sobolevConjugate d 2) =
        (eLpNormOn U (ENNReal.ofReal q) u.toFun).toReal ^ 2 := by
          simpa only [q] using hValuePower
    _ ≤ ((zeroBoundarySobolevConstantTwo d : ℝ) *
          (euclideanFieldELpNormOn U 2 u.grad).toReal) ^ 2 := hSobSq
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          (euclideanFieldELpNormOn U 2 u.grad).toReal ^ 2 := by ring
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ∫ x in U, vecNormSq (u.grad x) ∂volume := by rw [hGradient]

/-- The critical Sobolev estimate with the De Giorgi exponent displayed as
`(d - 2) / d`. -/
theorem setIntegral_abs_rpow_sobolevConjugate_two_rpow_sub_div_le
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (u : H10Function U) :
    (∫ x in U, |u.toFun x| ^ (sobolevConjugate d 2) ∂volume) ^
        (((d : ℝ) - 2) / (d : ℝ)) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ∫ x in U, vecNormSq (u.grad x) ∂volume := by
  rw [← two_div_sobolevConjugate_two hd]
  exact setIntegral_abs_rpow_sobolevConjugate_two_rpow_two_div_le hd u

/-- The same critical estimate with both exponents expanded for direct use in
the nonlinear De Giorgi recurrence. -/
theorem setIntegral_abs_rpow_two_mul_div_sub_two_rpow_sub_div_le
    {d : ℕ} (hd : 3 ≤ d) {U : Set (Vec d)}
    (u : H10Function U) :
    (∫ x in U,
        |u.toFun x| ^ ((2 : ℝ) * d / ((d : ℝ) - 2)) ∂volume) ^
        (((d : ℝ) - 2) / (d : ℝ)) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ∫ x in U, vecNormSq (u.grad x) ∂volume := by
  simpa only [sobolevConjugate, mul_comm] using
    setIntegral_abs_rpow_sobolevConjugate_two_rpow_sub_div_le hd u

end PDE
