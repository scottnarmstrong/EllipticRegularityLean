module

public import PDEFoundation.Euler.TimeKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Diagonal limit of the time mollifier

For `f` locally integrable, `∫ σ, η_n(σ - τ) f(σ) → f(τ)` for a.e. `τ` (Lebesgue differentiation through
the Mathlib theorem for bump families).  Consequently, for a bilinear form
`Φ(τ,σ) = ∫_Ω a(ω,τ) b(ω,σ) dμ(ω)` with `a`, `b` bounded and jointly a.e. strongly measurable,
`∫ g(τ) ∫ η_n(σ-τ) Φ(τ,σ) dσ dτ → ∫ g(τ) Φ(τ,τ) dτ` for continuous `g`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology Convolution

namespace PDE

theorem etaK_conv_eq (n : ℕ) (f : ℝ → ℝ) (τ : ℝ) :
    ((timeBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℝ)] f) τ =
      ∫ σ, etaK n (σ - τ) * f σ := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun σ => etaK n (σ - τ) * f σ) volume τ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel_left, etaK_neg]
  rfl

theorem ae_tendsto_timeMollify {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ τ ∂(volume : Measure ℝ),
      Tendsto (fun n => ∫ σ, etaK n (σ - τ) * f σ) atTop (𝓝 (f τ)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℝ)) (φ := timeBump) (l := atTop) (K := 2) (g := f)
    tendsto_tDelta (Filter.Eventually.of_forall fun n => by
      show tDelta n ≤ 2 * (tDelta n / 2)
      linarith) hf
  filter_upwards [h] with τ hτ
  exact hτ.congr (fun n => etaK_conv_eq n f τ)

theorem abs_timeMollify_le {T : ℝ} {f : ℝ → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hf : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) T)))
    (hB : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) T)), |f σ| ≤ B) (n : ℕ) (τ : ℝ) :
    |∫ σ, etaK n (σ - τ) * f σ ∂(volume.restrict (Icc (0 : ℝ) T))| ≤ B := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hηs : Integrable (fun σ => etaK n (σ - τ)) volume :=
    (etaK_integrable n).comp_sub_right τ
  have hηB : Integrable (fun σ => etaK n (σ - τ) * B) ν := (hηs.mul_const B).restrict
  have hmeas : AEStronglyMeasurable (fun σ => etaK n (σ - τ) * f σ) ν :=
    (((etaK_contDiff n).continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).mul hf
  have hint : Integrable (fun σ => etaK n (σ - τ) * f σ) ν := by
    refine Integrable.mono' hηB hmeas ?_
    filter_upwards [hB] with σ hσ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (etaK_nonneg n _)]
    exact mul_le_mul_of_nonneg_left hσ (etaK_nonneg n _)
  calc |∫ σ, etaK n (σ - τ) * f σ ∂ν| ≤ ∫ σ, |etaK n (σ - τ) * f σ| ∂ν := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun σ => etaK n (σ - τ) * f σ)
    _ ≤ ∫ σ, etaK n (σ - τ) * B ∂ν := by
        refine integral_mono_ae hint.abs hηB ?_
        filter_upwards [hB] with σ hσ
        rw [abs_mul, abs_of_nonneg (etaK_nonneg n _)]
        exact mul_le_mul_of_nonneg_left hσ (etaK_nonneg n _)
    _ ≤ ∫ σ, etaK n (σ - τ) * B := by
        refine setIntegral_le_integral (hηs.mul_const B) ?_
        exact Filter.Eventually.of_forall fun σ => mul_nonneg (etaK_nonneg n _) hB0
    _ = B := by
        rw [integral_mul_const, integral_sub_right_eq_self (etaK n) τ, etaK_integral, one_mul]

end PDE
