module

public import PDEFoundation.Measure.NormalizedLp

/-! # Transport of normalized local `Lᵖ` bounds -/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

/-- A normalized local `Lᵖ` estimate transfers to raw restricted volume when
its output domain has no larger volume than its input domain. -/
theorem eLpNorm_le_of_eLpMeanNorm_le_of_volume_le
    {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {U V : Set (Vec d)} (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (hVPos : 0 < volume V) (hVTop : volume V < ∞) (hVU : volume V ≤ volume U)
    {p : ENNReal} {f : Vec d → E} {g : Vec d → F} {K : ENNReal}
    (h : eLpNorm f p (normalizedVolumeOn V) ≤
      K * eLpNorm g p (normalizedVolumeOn U)) :
    eLpNorm f p (volumeOn V) ≤ K * eLpNorm g p (volumeOn U) := by
  have hr : 0 ≤ (1 / p).toReal := ENNReal.toReal_nonneg
  have hpow : volume V ^ (1 / p).toReal ≤ volume U ^ (1 / p).toReal :=
    ENNReal.rpow_le_rpow hVU hr
  rw [show eLpNorm f p (volumeOn V) =
      volume V ^ (1 / p).toReal * eLpNorm f p (normalizedVolumeOn V) by
        simpa only [eLpNormOn, eLpMeanNormOn] using
          eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hVPos hVTop p f,
    show eLpNorm g p (volumeOn U) =
      volume U ^ (1 / p).toReal * eLpNorm g p (normalizedVolumeOn U) by
        simpa only [eLpNormOn, eLpMeanNormOn] using
          eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hUPos hUTop p g]
  calc
    volume V ^ (1 / p).toReal * eLpNorm f p (normalizedVolumeOn V) ≤
        volume V ^ (1 / p).toReal *
          (K * eLpNorm g p (normalizedVolumeOn U)) :=
      mul_le_mul_right h _
    _ = K * (volume V ^ (1 / p).toReal *
          eLpNorm g p (normalizedVolumeOn U)) := by ac_rfl
    _ ≤ K * (volume U ^ (1 / p).toReal *
          eLpNorm g p (normalizedVolumeOn U)) := by
      exact mul_le_mul_right (mul_le_mul_left hpow _) _

/-- The guarded real normalized `Lᵖ` norm is the raw norm multiplied by the
exact negative volume power. -/
theorem lpMeanNormOn_eq_volume_toReal_neg_rpow_mul_eLpNorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (p : ENNReal) (f : Vec d → E) (hf : MemLp f p (volumeOn U)) :
    lpMeanNormOn U p f (memLp_normalizedVolumeOn_of_memLpOn hf hUPos) =
      (volume U).toReal ^ (-(1 / p).toReal) *
        (eLpNorm f p (volumeOn U)).toReal := by
  rw [lpMeanNormOn_eq_toReal]
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop p f]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_inv, ← Real.rpow_neg_eq_inv_rpow]
  rfl

end

end PDE
