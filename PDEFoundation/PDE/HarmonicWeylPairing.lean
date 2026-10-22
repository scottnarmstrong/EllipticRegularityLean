module

public import PDEFoundation.PDE.HarmonicWeylRepresentative
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Pairing a symmetric compact convolution against a test function -/

@[expose] public section

namespace PDE

open MeasureTheory Metric
open scoped Convolution

noncomputable section

variable {d : ℕ}

/-- Fubini and symmetry move a compact even kernel from a locally integrable
function onto a continuous compact test function. -/
theorem integral_harmonicConvolution_mul_test
    {K g ψ : Vec d → ℝ}
    (hKs : HasCompactSupport K) (hKc : Continuous K)
    (hKeven : ∀ y, K (-y) = K y)
    (hg : LocallyIntegrable g volume)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    (∫ x, (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x * ψ x) =
      ∫ y, g y * (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y := by
  obtain ⟨CK, hCK⟩ := hKs.exists_bound_of_continuous hKc
  obtain ⟨R, hR⟩ := hψs.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨D, hD⟩ := hKs.isBounded.subset_closedBall (0 : Vec d)
  have hbound (x y : Vec d) :
      ‖K (x - y) * g y * ψ x‖ ≤
        CK * ‖ψ x‖ *
          (Metric.closedBall (0 : Vec d) (R + D)).indicator (fun z => ‖g z‖) y := by
    by_cases hy : y ∈ Metric.closedBall (0 : Vec d) (R + D)
    · rw [Set.indicator_of_mem hy]
      simp only [norm_mul]
      calc
        ‖K (x - y)‖ * ‖g y‖ * ‖ψ x‖ ≤ CK * ‖g y‖ * ‖ψ x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCK (x - y)) (norm_nonneg _)) (norm_nonneg _)
        _ = CK * ‖ψ x‖ * ‖g y‖ := by ring
    · by_cases hψzero : ψ x = 0
      · simp [hψzero]
      · have hxR : ‖x‖ ≤ R := by
          have hxt : x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hψzero)
          simpa [Metric.mem_closedBall, dist_zero_right] using hR hxt
        have hyR : R + D < ‖y‖ := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hy
        have hKzero : K (x - y) = 0 := by
          by_contra hk
          have hkt : x - y ∈ tsupport K :=
            subset_tsupport K (Function.mem_support.mpr hk)
          have hnorm : ‖x - y‖ ≤ D := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hD hkt
          have htri : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
            have hdecomp : y = -(x - y) + x := by abel
            calc
              ‖y‖ = ‖-(x - y) + x‖ := congrArg norm hdecomp
              _ ≤ ‖x - y‖ + ‖x‖ := by
                simpa only [norm_neg] using norm_add_le (-(x - y)) x
          linarith
        rw [Set.indicator_of_notMem hy, hKzero]
        simp
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y : Vec d => K (x - y) * g y * ψ x)
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable
        (fun z : Vec d × Vec d => K (z.1 - z.2)) (volume.prod volume) :=
      (hKc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun z : Vec d × Vec d => g z.2) (volume.prod volume) :=
      hg.aestronglyMeasurable.comp_snd
    have h3 : AEStronglyMeasurable
        (fun z : Vec d × Vec d => ψ z.1) (volume.prod volume) :=
      (hψc.comp continuous_fst).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  have hint : Integrable
      (Function.uncurry fun x y : Vec d => K (x - y) * g y * ψ x)
      (volume.prod volume) := by
    refine Integrable.mono' ?_ hmeas
      (Filter.Eventually.of_forall fun z => hbound z.1 z.2)
    exact Integrable.mul_prod
      ((hψc.integrable_of_hasCompactSupport hψs).norm.const_mul CK)
      (MeasureTheory.IntegrableOn.integrable_indicator
        ((hg.integrableOn_isCompact (isCompact_closedBall (0 : Vec d) (R + D))).norm)
        measurableSet_closedBall)
  have hswap := integral_integral_swap
    (μ := (volume : Measure (Vec d))) (ν := (volume : Measure (Vec d))) hint
  calc
    (∫ x, (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x * ψ x) =
        ∫ x, ∫ y, K (x - y) * g y * ψ x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [MeasureTheory.convolution_eq_swap]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, integral_mul_const]
    _ = ∫ y, ∫ x, K (x - y) * g y * ψ x := hswap
    _ = ∫ y, g y * (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [MeasureTheory.convolution_eq_swap]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have hsub : x - y = -(y - x) := by abel
      rw [hsub, hKeven]
      ring

end

end PDE
