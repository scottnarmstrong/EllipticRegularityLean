module

public import PDEFoundation.Euler.PeriodicCZTile
public import PDEFoundation.Euler.SmoothIdentities
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify

/-!
# Spatial mollification of periodic fields: basic properties

`mollify a f = molK a ⋆ f` is whole-space convolution with the scaled unit kernel `molK a` (nonnegative,
smooth, mass one, supported in `{‖y‖ ≤ a}`).  For a periodic locally integrable `f` it is smooth, periodic,
and bounded by `B` whenever `|f| ≤ B` a.e.  `IsTorusPeriodic.locallyIntegrable` turns `L¹(cube)` into local
integrability of the periodic extension.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

/-- The scaled mollifier. -/
noncomputable def molK (a : ℝ) : Vec 2 → ℝ :=
  scaledConvexApproxKernel (unitConvexApproxKernel (d := 2)) a

theorem molK_nonneg {a : ℝ} (ha : 0 < a) (y : Vec 2) : 0 ≤ molK a y :=
  scaledConvexApproxKernel_nonneg isConvexApproxKernel_unitConvexApproxKernel ha y

theorem molK_integrable {a : ℝ} (ha : 0 < a) : Integrable (molK a) :=
  integrable_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel ha

theorem molK_integral {a : ℝ} (ha : 0 < a) : ∫ y, molK a y = 1 :=
  integral_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel ha

theorem molK_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (molK a) :=
  contDiff_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel a

theorem molK_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (molK a) :=
  hasCompactSupport_scaledConvexApproxKernel
    isConvexApproxKernel_unitConvexApproxKernel.compactSupport ha

theorem molK_eq_zero {a : ℝ} (ha : 0 < a) {y : Vec 2} (hy : a < ‖y‖) : molK a y = 0 :=
  scaledUnitKernel_eq_zero_of_lt_norm ha hy

/-- Spatial mollification `f ↦ molK a ⋆ f`. -/
noncomputable def mollify (a : ℝ) (f : Vec 2 → ℝ) : Vec 2 → ℝ := wholeSpaceMollify a f

theorem mollify_apply (a : ℝ) (f : Vec 2 → ℝ) (x : Vec 2) :
    mollify a f x = ∫ t, molK a t * f (x - t) := by
  simp [mollify, wholeSpaceMollify, convolution_def, molK]

theorem mollify_contDiff {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify a f) :=
  HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (molK_hasCompactSupport ha)
    (molK_contDiff a) hf

theorem mollify_periodic {a : ℝ} {f : Vec 2 → ℝ} (hf : IsTorusPeriodic f) :
    IsTorusPeriodic (mollify a f) := by
  intro i x
  rw [mollify_apply, mollify_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [show x + basisVec i - t = (x - t) + basisVec i by abel, hf i]

theorem molK_convolutionExists {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ}
    (hf : LocallyIntegrable f volume) :
    ConvolutionExists (molK a) f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  (molK_hasCompactSupport ha).convolutionExists_left _ (molK_contDiff a).continuous hf

theorem integrable_molK_mul {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume)
    (x : Vec 2) : Integrable (fun t => molK a t * f (x - t)) := by
  have := molK_convolutionExists ha hf x
  simpa [ConvolutionExistsAt] using this

theorem abs_mollify_le {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume) {B : ℝ}
    (hB : ∀ᵐ y, |f y| ≤ B) (x : Vec 2) : |mollify a f x| ≤ B := by
  have hK := molK_integrable ha
  have hex := integrable_molK_mul ha hf x
  rw [mollify_apply]
  calc |∫ t, molK a t * f (x - t)| ≤ ∫ t, |molK a t * f (x - t)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t => molK a t * f (x - t))
    _ ≤ ∫ t, molK a t * B := by
        refine integral_mono_ae hex.abs (hK.mul_const B) ?_
        have hB' : ∀ᵐ t ∂(volume : Measure (Vec 2)), |f (x - t)| ≤ B := by
          have := ((volume : Measure (Vec 2)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hB
          exact this
        filter_upwards [hB'] with t ht
        rw [abs_mul, abs_of_nonneg (molK_nonneg ha t)]
        exact mul_le_mul_of_nonneg_left ht (molK_nonneg ha t)
    _ = B := by rw [integral_mul_const, molK_integral ha, one_mul]

end PDE
