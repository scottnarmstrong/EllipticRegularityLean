module

public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.NormalizedLp

/-! # Normalization on the half ball -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

/-- The exact half-ball probability measure in fixed unit-ball normalization. -/
theorem normalizedVolumeOn_halfBall_eq_fixedUnit_smul (d : ℕ) :
    normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2)) =
      ENNReal.ofReal ((2 : ℝ)^d) •
        ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
          volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  rw [normalizedVolumeOn, smul_smul,
    volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec d) (by norm_num),
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num : (0:ℝ)<1/2) d)).ne') (Or.inl ENNReal.ofReal_ne_top)]
  congr 2
  rw [← ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num) d)]
  congr 1
  rw [← inv_pow]
  norm_num

/-- Exact real norm conversion, with genuine local membership supplying finiteness. -/
theorem eLpNorm_normalized_halfBall_toReal_eq {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] (f : Vec d → E)
    {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    (eLpNorm f (ENNReal.ofReal p)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal =
      (2 : ℝ)^((d : ℝ)/p) *
      (eLpNorm f (ENNReal.ofReal p)
        ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
          volumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal := by
  have hfinite := hf.smul_measure
    (ENNReal.inv_ne_top.mpr (volume_euclideanBall_pos (0 : Vec d) (by norm_num : (0:ℝ)<1)).ne')
  have hnfinite := hf.smul_measure
    (ENNReal.inv_ne_top.mpr (volume_euclideanBall_pos (0 : Vec d) (by norm_num : (0 : ℝ)<1/2)).ne')
  rw [normalizedVolumeOn_halfBall_eq_fixedUnit_smul,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) d)).ne']
  simp only [smul_eq_mul, one_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0:ℝ)≤2) d)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_eq_mul_inv]

/-- For high exponents the normalization costs only a dimension-dependent factor. -/
theorem eLpNorm_normalized_halfBall_toReal_le {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] (f : Vec d → E)
    {p : ℝ} (hp : 4 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) :
    (eLpNorm f (ENNReal.ofReal p)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
      (2 : ℝ)^((d : ℝ)/4) *
      (eLpNorm f (ENNReal.ofReal p)
        ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
          volumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal := by
  rw [eLpNorm_normalized_halfBall_toReal_eq f (by linarith) hf]
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hp

end PDE
