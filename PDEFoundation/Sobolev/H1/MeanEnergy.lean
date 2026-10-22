module

public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Measure.BallVolume

/-!
# Mean Euclidean gradient energy and domain restriction

The square root of mean energy is the raw energy norm divided by the square
root of volume. Restriction retains the exact volume ratio; no comparison
between the native supremum norm and the Euclidean gradient norm is used.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Exact conversion between mean energy and raw energy. -/
theorem sqrt_integralAverage_vecNormSq_eq
    (U : Set (Vec d)) (F : Vec d → Vec d) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (F x))) =
      Real.sqrt (∫ x in U, vecNormSq (F x)) / Real.sqrt (volume U).toReal := by
  rw [integralAverage, Real.sqrt_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    Real.sqrt_inv]
  exact mul_comm _ _

/-- Restricting the raw energy decreases it. -/
theorem setIntegral_vecNormSq_mono_set
    {U V : Set (Vec d)} (hUV : U ⊆ V) {F : Vec d → Vec d}
    (hF : MemVectorL2On V F) :
    (∫ x in U, vecNormSq (F x)) ≤ ∫ x in V, vecNormSq (F x) :=
  setIntegral_mono_set (integrableOn_vecNormSq_of_memVectorL2On hF)
    (Filter.Eventually.of_forall fun x => vecNormSq_nonneg (F x)) hUV.eventuallyLE

/-- Mean energy under restriction has precisely the square-root volume cost. -/
theorem sqrt_integralAverage_vecNormSq_mono_set
    {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hVpos : 0 < (volume V).toReal) {F : Vec d → Vec d}
    (hF : MemVectorL2On V F) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (F x))) ≤
      (Real.sqrt (volume V).toReal / Real.sqrt (volume U).toReal) *
        Real.sqrt (integralAverage V (fun x => vecNormSq (F x))) := by
  rw [sqrt_integralAverage_vecNormSq_eq, sqrt_integralAverage_vecNormSq_eq]
  have hv : Real.sqrt (volume V).toReal ≠ 0 := (Real.sqrt_pos.mpr hVpos).ne'
  have hraw := Real.sqrt_le_sqrt (setIntegral_vecNormSq_mono_set hUV hF)
  calc
    Real.sqrt (∫ x in U, vecNormSq (F x)) / Real.sqrt (volume U).toReal ≤
        Real.sqrt (∫ x in V, vecNormSq (F x)) / Real.sqrt (volume U).toReal :=
      div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
    _ = (Real.sqrt (volume V).toReal / Real.sqrt (volume U).toReal) *
        (Real.sqrt (∫ x in V, vecNormSq (F x)) / Real.sqrt (volume V).toReal) := by
      field_simp

/-- The exact volume loss in the dyadic ball restriction. -/
theorem sqrt_volume_euclideanBall_div_half (z : Vec d) {R : ℝ} (hR : 0 < R) :
    Real.sqrt (volume (euclideanBall z R)).toReal /
      Real.sqrt (volume (euclideanBall z (R / 2))).toReal =
        (2 : ℝ) ^ ((d : ℝ) / 2) := by
  rw [← Real.sqrt_div ENNReal.toReal_nonneg,
    volume_euclideanBall_toReal_div_eq_div_pow z z (by positivity) hR]
  have hratio : R / (R / 2) = (2 : ℝ) := by field_simp
  rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Dyadic restriction of mean energy, retaining precisely `2^(d/2)`. -/
theorem sqrt_integralAverage_vecNormSq_euclideanBall_half_le
    {z : Vec d} {R : ℝ} (hR : 0 < R) {F : Vec d → Vec d}
    (hF : MemVectorL2On (euclideanBall z R) F) :
    Real.sqrt (integralAverage (euclideanBall z (R / 2)) (fun x => vecNormSq (F x))) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (F x))) := by
  have h := sqrt_integralAverage_vecNormSq_mono_set
    (euclideanBall_mono (x₀ := z) (by positivity) (by linarith : R / 2 ≤ R))
    (volume_euclideanBall_toReal_pos z hR) hF
  simpa only [sqrt_volume_euclideanBall_div_half z hR] using h

end

end PDE
