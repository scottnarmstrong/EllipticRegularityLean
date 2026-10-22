module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareNormalizedLayerFunction
public import PDEFoundation.Sobolev.Inequalities.ConvexRiesz
public import PDEFoundation.Analysis.RieszWeakTypeBound
public import PDEFoundation.Measure.EuclideanVectorIntegral

/-!
# The measure of a dyadic superlevel set from the Riesz potential bound

For a `W^{1,1}` function `v` vanishing on a measurable set `S` of positive measure in a bounded
open convex domain `W`, the Riesz potential bound applied to the dyadic layer
`min ((v - a)_+, a)` and the weak-type bound for the Riesz potential control
`|{v ≥ 2 a}|` by the `L¹` norm of the gradient of the layer.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ} {W : Set (Vec d)}

/-- Measure of a dyadic superlevel set (Step 1 of Theorem 1.9). -/
theorem volumeOn_setOf_two_mul_le_layer (hd : 2 ≤ d) (hW : IsOpenBoundedConvexDomain W)
    {D M : ℝ} (hWD : HasEuclideanDiameterLE W D) {S : Set (Vec d)} (hSm : MeasurableSet S)
    (hSW : S ⊆ W) (hSpos : 0 < volume S) (hM : 0 < M)
    (hMS : D ^ d / (d * (volume S).toReal) ≤ M)
    (v : W1pFunction W 1) (hS0 : ∀ x ∈ S, v.toFun x = 0) {a : ℝ} (ha : 0 < a) :
    volumeOn W {x | 2 * a ≤ v.toFun x} ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / (d - 1)) * d * (volume (euclideanBall (0 : Vec d) 1)).toReal) *
        (ENNReal.ofReal (M / a) *
          ∫⁻ y in W, ENNReal.ofReal (vecEuclideanNorm ((v.layer hW a).grad y))) ^
            ((d : ℝ) / (d - 1)) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have := hW.isFiniteMeasure_volumeOn
  set vk := v.layer hW a with hvk
  have hint : Integrable (fun y => vecEuclideanNorm (vk.grad y)) (volumeOn W) :=
    integrable_vecEuclideanNorm_of_coord vk.grad fun i => (vk.grad_memLp i).integrable le_rfl
  let f : Vec d → ℝ := W.indicator (fun y => vecEuclideanNorm (vk.grad y))
  have hf0 : ∀ y, 0 ≤ f y := fun y =>
    Set.indicator_nonneg (fun _ _ => vecEuclideanNorm_nonneg _) y
  have hfint : Integrable f := (integrable_indicator_iff hW.measurableSet).2 hint
  have hI : ENNReal.ofReal (∫ y, f y) =
      ∫⁻ y in W, ENNReal.ofReal (vecEuclideanNorm (vk.grad y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall hf0),
      ← lintegral_indicator hW.measurableSet]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ W <;> simp [f, hy]
  have hR := abs_sub_integralAverage_ae_le_riesz hW hWD vk hSm hSW hSpos
  have havg : integralAverage S vk.toFun = 0 := by
    unfold integralAverage
    rw [setIntegral_congr_fun hSm (g := fun _ => 0)
      (fun x hx => W1pFunction.layer_eq_zero hW v ha.le (hS0 x hx))]
    simp
  have hRpot : ∀ x, ∫ y in W, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
      vecEuclideanNorm (vk.grad y) = rieszPotentialOne f x := by
    intro x
    unfold rieszPotentialOne rieszKernelOne
    rw [← integral_indicator hW.measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ W <;> simp [f, hy]
  have hpt : ∀ᵐ x ∂volumeOn W, 2 * a ≤ v.toFun x → a / M ≤ rieszPotentialOne f x := by
    filter_upwards [hR] with x hx h2
    rw [havg, sub_zero, abs_of_nonneg (W1pFunction.layer_nonneg hW v ha.le x), hRpot] at hx
    have hpot0 : 0 ≤ rieszPotentialOne f x :=
      integral_nonneg fun y => mul_nonneg (rieszKernelOne_nonneg _) (hf0 y)
    have hvx : vk.toFun x = a := W1pFunction.layer_eq_of_le hW v h2 ha.le
    rw [hvx] at hx
    rw [div_le_iff₀ hM]
    nlinarith [mul_le_mul_of_nonneg_right hMS hpot0]
  have hw := volume_setOf_le_rieszPotentialOne hd hf0 hfint (l := a / M) (by positivity)
  have hd1 : (0 : ℝ) ≤ (d : ℝ) / (d - 1) := by
    apply div_nonneg <;> linarith
  calc volumeOn W {x | 2 * a ≤ v.toFun x}
      ≤ volumeOn W {x | a / M ≤ rieszPotentialOne f x} :=
        measure_mono_ae (hpt.mono fun x hx h => hx h)
    _ ≤ volume {x | a / M ≤ rieszPotentialOne f x} := Measure.restrict_le_self _
    _ ≤ _ := hw
    _ = _ := by
      have hω : 0 ≤ (volume (euclideanBall (0 : Vec d) 1)).toReal := ENNReal.toReal_nonneg
      have hI0 : 0 ≤ ∫ y, f y := integral_nonneg hf0
      have hMa : 0 ≤ M / a := by positivity
      rw [ENNReal.ofReal_mul (by positivity), ← hI,
        ← ENNReal.ofReal_mul hMa, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hd1]
      congr 3
      field_simp

end PDE
