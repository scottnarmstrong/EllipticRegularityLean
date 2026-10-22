module

public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Linear changes of variables on native vector domains

The determinant factors are kept explicit. These identities also apply to
ellipsoids obtained as linear images of the round-ball geometry.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The exact Jacobian for an invertible native linear change of variables. -/
theorem map_linearEquiv_volume
    (e : Vec d ≃L[ℝ] Vec d) :
    Measure.map e (volume : Measure (Vec d)) =
      ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| • volume := by
  exact Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := e.toLinearMap) (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')

/-- The Jacobian identity with both domain restrictions transported exactly. -/
theorem map_linearEquiv_volumeOn
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    Measure.map e (volumeOn U) =
      ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| • volumeOn (e '' U) := by
  have hrestrict : (volume.restrict U).map e =
      (volume.map e).restrict (e '' U) := by
    have h := (e.toHomeomorph.toMeasurableEquiv.restrict_map
      (μ := volume) (s := e '' U)).symm
    change (volume.restrict (e ⁻¹' (e '' U))).map e =
      (volume.map e).restrict (e '' U) at h
    rw [Set.preimage_image_eq _ e.injective] at h
    exact h
  rw [volumeOn, hrestrict, map_linearEquiv_volume, Measure.restrict_smul]

/-- Exact integral transport, valid for real or vector-valued integrands. -/
theorem setIntegral_comp_linearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in U, f (e x) =
      |(LinearMap.det e.toLinearMap)⁻¹| • ∫ y in e '' U, f y := by
  have hmap := map_linearEquiv_volumeOn e U
  have h := e.toHomeomorph.measurableEmbedding.integral_map
    (μ := volumeOn U) f
  change (∫ y, f y ∂Measure.map e (volumeOn U)) =
    ∫ x, f (e x) ∂volumeOn U at h
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  exact h.symm

/-- Pulling back an `Lᵖ` field through an invertible linear map preserves
membership on the exact transported domain. -/
theorem memLpOn_comp_linearEquiv
    {E : Type*} [NormedAddCommGroup E]
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} (hf : MemLp f p (volumeOn (e '' U))) :
    MemLp (fun x => f (e x)) p (volumeOn U) := by
  apply MemLp.comp_of_map _ e.continuous.measurable.aemeasurable
  rw [map_linearEquiv_volumeOn]
  exact hf.smul_measure ENNReal.ofReal_ne_top

end PDE
