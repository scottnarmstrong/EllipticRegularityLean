module

public import PDEFoundation.PDE.HarmonicWeylPairing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Distributional convergence of harmonic mollifications -/

@[expose] public section

namespace PDE

open MeasureTheory Metric Filter
open scoped Convolution Topology

noncomputable section

variable {d : ℕ}

private theorem harmonicKernelScaled_convolution_test_bound
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ y, ‖ψ y‖ ≤ M) {δ : ℝ} (hδ : 0 < δ) (y : Vec d) :
    ‖(harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y‖ ≤ M := by
  have hsupport : Function.support (harmonicKernelScaled (d := d) δ) ⊆
      Metric.ball (0 : Vec d) δ := by
    intro z hz
    exact euclideanBall_subset_supBall hδ
      ((harmonicKernelScaled_tsupport_subset hδ) (subset_tsupport _ hz))
  have h := MeasureTheory.dist_convolution_le
    (μ := (volume : Measure (Vec d))) (f := harmonicKernelScaled δ) (g := ψ)
    (x₀ := y) (z₀ := (0 : ℝ)) (R := δ) (ε := M)
    (by exact (norm_nonneg _).trans (hM y)) hsupport
    (harmonicKernelScaled_nonneg hδ)
    (harmonicKernelScaled_integral_eq_one hδ)
    hψ.aestronglyMeasurable (fun z _ => by simpa [Real.dist_eq] using hM z)
  simpa [Real.dist_eq] using h

private theorem harmonicKernelScaled_convolution_test_zero_outside
    {ψ : Vec d → ℝ} (_hψs : HasCompactSupport ψ)
    {R δ : ℝ} (hR : tsupport ψ ⊆ Metric.closedBall (0 : Vec d) R)
    (hδ : 0 < δ) (hδone : δ < 1)
    {y : Vec d} (hy : y ∉ Metric.closedBall (0 : Vec d) (R + 1)) :
    (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y = 0 := by
  rw [MeasureTheory.convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply integral_eq_zero_of_ae
  filter_upwards with z
  by_cases hψzero : ψ z = 0
  · simp [hψzero]
  · have hzR : ‖z‖ ≤ R := by
      have hzt : z ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hψzero)
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hzt
    have hyR : R + 1 < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hKzero : harmonicKernelScaled δ (y - z) = 0 := by
      by_contra hk
      have hts : y - z ∈ tsupport (harmonicKernelScaled δ) :=
        subset_tsupport _ (Function.mem_support.mpr hk)
      have heuc : y - z ∈ euclideanBall (0 : Vec d) δ :=
        harmonicKernelScaled_tsupport_subset hδ hts
      have hnorm := (norm_le_vecEuclideanNorm (y - z)).trans_lt
        (by simpa only [sub_zero] using
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt
            (x₀ := 0) (x := y - z) hδ).mp heuc))
      have htri : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        have hdecomp : y = (y - z) + z := by abel
        calc
          ‖y‖ = ‖(y - z) + z‖ := congrArg norm hdecomp
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      linarith
    simp [hKzero]

/-- Pairing the harmonic mollification with a smooth compactly supported test
converges to pairing the original H¹ representative on its open domain. -/
theorem integral_harmonicMollify_mul_test_tendsto
    {U : Set (Vec d)} (hU : IsOpen U) (u : H1Function U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψs : HasCompactSupport ψ) (_hψU : tsupport ψ ⊆ U) :
    Tendsto (fun δ : ℝ => ∫ x, harmonicMollify u δ x * ψ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in U, u.toFun x * ψ x)) := by
  let g : Vec d → ℝ := Set.indicator U u.toFun
  have hg : LocallyIntegrable g volume := by
    have hmem : MemLp g 2 volume := by
      change MemLp (Set.indicator U u.toFun) 2 volume
      rw [memLp_indicator_iff_restrict hU.measurableSet]
      exact u.memL2
    exact hmem.locallyIntegrable (by norm_num)
  have hψc : Continuous ψ := hψ.continuous
  obtain ⟨M, hM⟩ := hψs.exists_bound_of_continuous hψc
  have hMnonneg : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  obtain ⟨R, hR⟩ := hψs.isBounded.subset_closedBall (0 : Vec d)
  let S : Set (Vec d) := Metric.closedBall (0 : Vec d) (R + 1)
  let B : Vec d → ℝ := fun y => M * S.indicator (fun z => ‖g z‖) y
  have hBint : Integrable B volume := by
    exact (MeasureTheory.IntegrableOn.integrable_indicator
      ((hg.integrableOn_isCompact (isCompact_closedBall (0 : Vec d) (R + 1))).norm)
      measurableSet_closedBall).const_mul M
  have hconvcont {δ : ℝ} (hδ : 0 < δ) :
      Continuous (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) := by
    exact (HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (harmonicKernelScaled_hasCompactSupport hδ)
      (harmonicKernelScaled_smooth δ)
      hψc.locallyIntegrable).continuous
  have hmeas : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun y => g y *
          (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y)
        volume := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hg.aestronglyMeasurable.mul (hconvcont hδ).aestronglyMeasurable
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂volume,
      ‖g y * (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y‖
        ≤ B y := by
    have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδone
    filter_upwards with y
    by_cases hy : y ∈ S
    · change ‖g y * (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y‖
          ≤ M * S.indicator (fun z => ‖g z‖) y
      rw [Set.indicator_of_mem hy]
      rw [norm_mul]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left
          (harmonicKernelScaled_convolution_test_bound hψc hM hδ y)
          (norm_nonneg (g y)))
    · have hzero := harmonicKernelScaled_convolution_test_zero_outside
        hψs hR hδ hδone hy
      rw [hzero]
      simp [B, Set.indicator_of_notMem hy]
  have hlim : ∀ᵐ y ∂volume,
      Tendsto (fun δ : ℝ => g y *
        (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y)
        (𝓝[>] (0 : ℝ)) (𝓝 (g y * ψ y)) := by
    filter_upwards with y
    exact tendsto_const_nhds.mul
      (harmonicKernelScaled_convolution_tendsto_right hψc y)
  have hDCT := tendsto_integral_filter_of_dominated_convergence B
    hmeas hbound hBint hlim
  have hpair : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ x, harmonicMollify u δ x * ψ x) =
        ∫ y, g y *
          (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) y := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact integral_harmonicConvolution_mul_test
      (harmonicKernelScaled_hasCompactSupport hδ)
      (harmonicKernelScaled_smooth δ).continuous
      (fun y => harmonicKernelScaled_neg y) hg hψc hψs
  have htarget : (∫ y, g y * ψ y) = ∫ y in U, u.toFun y * ψ y := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ U
    · simp [g, Set.indicator_of_mem hy]
    · simp [g, Set.indicator_of_notMem hy]
  rw [← htarget]
  exact hDCT.congr' (hpair.mono fun _ h => h.symm)

end

end PDE
