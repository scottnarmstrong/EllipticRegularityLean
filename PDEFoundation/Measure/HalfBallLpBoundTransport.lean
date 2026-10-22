module

public import PDEFoundation.Measure.HalfBallNormalization

/-! # Raw-to-normalized transport between the unit and half balls -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A raw `Lᵖ` bound from the unit ball to the half ball gives a guarded
normalized real bound, with a dimension-only loss uniform for `p ≥ 2`. -/
theorem lpMeanNormOn_halfBall_le_two_rpow_mul_of_eLpNorm_le
    {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p K : ℝ} (hp : 2 ≤ p) (hK : 0 ≤ K)
    (f : Vec d → E) (g : Vec d → F)
    (hf : MemLp f (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))))
    (hg : MemLp g (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hraw : eLpNorm f (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal K * eLpNorm g (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) 1))) :
    lpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p) f
        (memLp_normalizedVolumeOn_of_memLpOn hf
          (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * K *
        lpMeanNormOn (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) g
          (memLp_normalizedVolumeOn_of_memLpOn hg
            (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) := by
  let c : ENNReal := (volume (euclideanBall (0 : Vec d) 1))⁻¹
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr
    (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num))
  have hcTop : c ≠ ∞ := ENNReal.inv_ne_top.mpr
    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)).ne'
  have hfixed : eLpNorm f (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
      ENNReal.ofReal K * eLpNorm g (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) 1)) := by
    rw [eLpNorm_smul_measure_of_ne_zero hc0,
      eLpNorm_smul_measure_of_ne_zero hc0]
    calc
      c ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm f (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        c ^ (1 / ENNReal.ofReal p).toReal *
          (ENNReal.ofReal K * eLpNorm g (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) 1))) :=
        mul_le_mul_right hraw _
      _ = ENNReal.ofReal K *
          (c ^ (1 / ENNReal.ofReal p).toReal *
            eLpNorm g (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1))) := by ac_rfl
  have hgFixed : MemLp g (ENNReal.ofReal p)
      (c • volumeOn (euclideanBall (0 : Vec d) 1)) := hg.smul_measure hcTop
  have hfixedReal :
      (eLpNorm f (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
      K * (eLpNorm g (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) 1))).toReal := by
    have htop : ENNReal.ofReal K * eLpNorm g (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgFixed.eLpNorm_ne_top
    have := ENNReal.toReal_mono htop hfixed
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using this
  rw [lpMeanNormOn_eq_toReal, lpMeanNormOn_eq_toReal]
  change (eLpNorm f (ENNReal.ofReal p)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
    (2 : ℝ) ^ ((d : ℝ) / 2) * K *
      (eLpNorm g (ENNReal.ofReal p)
        (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))).toReal
  rw [eLpNorm_normalized_halfBall_toReal_eq f (by linarith) hf]
  change (2 : ℝ) ^ ((d : ℝ) / p) *
      (eLpNorm f (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
    (2 : ℝ) ^ ((d : ℝ) / 2) * K *
      (eLpNorm g (ENNReal.ofReal p)
        (c • volumeOn (euclideanBall (0 : Vec d) 1))).toReal
  calc
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / p) *
        (K * (eLpNorm g (ENNReal.ofReal p)
          (c • volumeOn (euclideanBall (0 : Vec d) 1))).toReal) :=
      mul_le_mul_of_nonneg_left hfixedReal (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) *
        (K * (eLpNorm g (ENNReal.ofReal p)
          (c • volumeOn (euclideanBall (0 : Vec d) 1))).toReal) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hp
      · exact mul_nonneg hK ENNReal.toReal_nonneg
    _ = _ := by ring

end

end PDE
