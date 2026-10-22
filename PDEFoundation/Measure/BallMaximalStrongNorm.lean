module

public import PDEFoundation.Measure.BallMaximalStrongMoment

/-! # Strong norm bound for the uncentered ball maximal function -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The uncentered Euclidean-ball maximal operator satisfies the strong
`L^q` seminorm bound obtained from its exact extended nonnegative moment
estimate. The maximal function remains `ℝ≥0∞` valued throughout. -/
theorem eLpNorm_uncenteredBallMaximal_le
    {d : ℕ} (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) volume) :
    eLpNorm (uncenteredBallMaximal b) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal
          (2 * (((3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q))) *
        eLpNorm b (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqNonneg : 0 ≤ q := hq0.le
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  have hpTop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hqNonneg
  have hmoment := lintegral_rpow_uncenteredBallMaximal_le b hq hb
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
      (measurable_uncenteredBallMaximal b).aestronglyMeasurable, hqReal]
  simp only [enorm_eq_self]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hb.aestronglyMeasurable, hqReal]
  simp_rw [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hqNonneg]
  apply (ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hqNonneg)).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hqNonneg)]
  congr 1
  have h3 : 0 < (3 : ℝ) ^ d := pow_pos (by norm_num) _
  have hbase : 0 < (3 : ℝ) ^ d * q / (q - 1) :=
    div_pos (mul_pos h3 hq0) (sub_pos.mpr hq)
  have hA : 0 ≤ (2 : ℝ) ^ q * (3 : ℝ) ^ d * q / (q - 1) :=
    (div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) h3.le)
      hqNonneg) (sub_pos.mpr hq).le)
  rw [ENNReal.ofReal_rpow_of_nonneg hA (one_div_nonneg.mpr hqNonneg)]
  apply congrArg ENNReal.ofReal
  calc
    ((2 : ℝ) ^ q * (3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q) =
        ((2 : ℝ) ^ q * ((3 : ℝ) ^ d * q / (q - 1))) ^ (1 / q) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ q) ^ (1 / q) *
        (((3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) hbase.le]
    _ = 2 * (((3 : ℝ) ^ d * q / (q - 1)) ^ (1 / q)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [mul_one_div_cancel hq0.ne']
      norm_num

end PDE
