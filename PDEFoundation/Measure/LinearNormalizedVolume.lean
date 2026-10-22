module

public import PDEFoundation.Measure.LinearAverage
public import PDEFoundation.Measure.NormalizedLp

/-! # Linear transport of normalized restricted volume -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Every native continuous linear equivalence pushes normalized restricted
volume to normalized volume on the exact image set. -/
theorem measurePreserving_linearEquiv_normalizedVolumeOn
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    MeasurePreserving e (normalizedVolumeOn U)
      (normalizedVolumeOn (e '' U)) := by
  let c : ENNReal := ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹|
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  have hc0 : c ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hdet))).ne'
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hvol : volume U = c * volume (e '' U) :=
    volume_eq_abs_inv_det_mul_volume_image e U
  have hcoef : (volume U)⁻¹ * c = (volume (e '' U))⁻¹ := by
    rw [hvol, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
    calc
      (c⁻¹ * (volume (e '' U))⁻¹) * c =
          (c⁻¹ * c) * (volume (e '' U))⁻¹ := by ac_rfl
      _ = (volume (e '' U))⁻¹ := by
        rw [ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
  refine ⟨e.continuous.measurable, ?_⟩
  rw [normalizedVolumeOn, normalizedVolumeOn,
    Measure.map_smul _ e.continuous.measurable.aemeasurable,
    map_linearEquiv_volumeOn]
  change (volume U)⁻¹ • (c • volumeOn (e '' U)) =
    (volume (e '' U))⁻¹ • volumeOn (e '' U)
  rw [smul_smul, hcoef]

/-- The inverse equivalence pushes normalized volume on an image set back to
normalized volume on the original set. -/
theorem measurePreserving_linearEquiv_symm_normalizedVolumeOn
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    MeasurePreserving e.symm (normalizedVolumeOn (e '' U))
      (normalizedVolumeOn U) := by
  have hset : e.symm '' (e '' U) = U := by
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      simpa only [e.symm_apply_apply] using hu
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  have h := measurePreserving_linearEquiv_normalizedVolumeOn e.symm (e '' U)
  convert h using 1
  · congr 2
    exact hset.symm

/-- Normalized `Lᵖ` seminorms are exactly invariant under pullback by a native
continuous linear equivalence. -/
theorem eLpMeanNormOn_comp_linearEquiv
    {E : Type*} [NormedAddCommGroup E]
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) (p : ENNReal)
    (f : Vec d → E)
    (hf : AEStronglyMeasurable f (normalizedVolumeOn (e '' U))) :
    eLpMeanNormOn U p (fun x => f (e x)) =
      eLpMeanNormOn (e '' U) p f := by
  simpa only [eLpMeanNormOn, Function.comp_apply] using!
    eLpNorm_comp_measurePreserving hf
      (measurePreserving_linearEquiv_normalizedVolumeOn e U)

end PDE
