module

public import PDEFoundation.Measure.LinearVolume
public import PDEFoundation.Sobolev.Mean

/-!
# Integral averages under invertible linear changes of variables

This file records the exact volume and arithmetic-average identities for a
native continuous linear equivalence.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The exact restricted-volume identity evaluated on the whole space. -/
theorem volume_eq_abs_inv_det_mul_volume_image
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    volume U = ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| * volume (e '' U) := by
  have h := congrArg (fun μ : Measure (Vec d) => μ Set.univ)
    (map_linearEquiv_volumeOn e U)
  change (Measure.map e (volumeOn U)) Set.univ =
    (ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| •
      volumeOn (e '' U)) Set.univ at h
  rw [Measure.map_apply e.continuous.measurable MeasurableSet.univ] at h
  rw [Measure.smul_apply, smul_eq_mul, Set.preimage_univ,
    Measure.restrict_apply_univ] at h
  simpa only [volumeOn, Measure.restrict_apply_univ] using h

/-- The volume of a linear image, with its exact Jacobian factor. -/
theorem volume_image_linearEquiv
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    volume (e '' U) =
      volume U / ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  have hc0 : ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hdet))).ne'
  exact (ENNReal.eq_div_iff hc0 ENNReal.ofReal_ne_top).2
    (volume_eq_abs_inv_det_mul_volume_image e U).symm

/-- Positive volume is preserved by an invertible linear image. -/
theorem volume_image_linearEquiv_pos
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)} (hU : 0 < volume U) :
    0 < volume (e '' U) := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  rw [volume_image_linearEquiv]
  exact ENNReal.div_pos hU.ne' ENNReal.ofReal_ne_top

/-- Finite volume is preserved by an invertible linear image. -/
theorem volume_image_linearEquiv_lt_top
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)} (hU : volume U < ∞) :
    volume (e '' U) < ∞ := by
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  have hc0 : ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hdet))).ne'
  rw [volume_image_linearEquiv]
  exact ENNReal.div_lt_top hU.ne hc0

/-- Arithmetic integral averages are invariant under an invertible linear
change of variables, on positive finite-volume sets. -/
theorem integralAverage_comp_linearEquiv
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)}
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (f : Vec d → ℝ) :
    integralAverage U (fun x => f (e x)) = integralAverage (e '' U) f := by
  let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
  have hdet : LinearMap.det e.toLinearMap ≠ 0 :=
    isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det'
  have hJ : 0 < J := abs_pos.mpr (inv_ne_zero hdet)
  have hImagePos : 0 < volume (e '' U) := volume_image_linearEquiv_pos e hUpos
  have hImageTop : volume (e '' U) < ∞ := volume_image_linearEquiv_lt_top e hUtop
  have hvol := volume_eq_abs_inv_det_mul_volume_image e U
  have hvolReal :
      (volume U).toReal = J * (volume (e '' U)).toReal := by
    have := congrArg ENNReal.toReal hvol
    simpa [J, ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ.le] using this
  have hUreal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUpos.ne' hUtop.ne).ne'
  have hImageReal : (volume (e '' U)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hImagePos.ne' hImageTop.ne).ne'
  have hint := setIntegral_comp_linearEquiv e U f
  change (∫ x in U, f (e x)) = J • ∫ y in e '' U, f y at hint
  rw [smul_eq_mul] at hint
  unfold integralAverage
  rw [hint, hvolReal]
  field_simp [hJ.ne', hUreal, hImageReal]

end PDE
