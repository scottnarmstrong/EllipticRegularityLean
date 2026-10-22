module

public import PDEFoundation.PDE.HarmonicWeylConsistency
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Almost everywhere convergence of the radial approximate identity -/

@[expose] public section

namespace PDE

open MeasureTheory Metric Filter
open scoped Convolution Topology

noncomputable section

variable {d : ℕ}

/-- The scaled round kernels recover a locally integrable function almost
everywhere as their scale tends to zero from above. -/
theorem ae_tendsto_harmonicKernelScaled_convolution_of_locallyIntegrable
    {g : Vec d → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun δ : ℝ =>
        (harmonicKernelScaled δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  obtain ⟨C₀, hC₀⟩ :=
    (harmonicKernel_hasCompactSupport (d := d)).exists_bound_of_continuous
      harmonicKernel_smooth.continuous
  have hC₀nonneg : 0 ≤ C₀ :=
    (norm_nonneg (harmonicKernel (0 : Vec d))).trans (hC₀ 0)
  let V : ℝ := (volume (Metric.closedBall (0 : Vec d) 1)).toReal
  have hVpos : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos
      (measure_closedBall_pos (volume : Measure (Vec d)) 0 (by norm_num)).ne'
      measure_closedBall_lt_top.ne
  have hvolume (x : Vec d) {δ : ℝ} (hδ : 0 < δ) :
      (volume (Metric.closedBall x δ)).toReal = δ ^ d * V := by
    have h := Measure.addHaar_real_closedBall' (volume : Measure (Vec d)) x hδ.le
    rw [show Module.finrank ℝ (Vec d) = d by simp [Vec]] at h
    simpa only [Measure.real, V] using h
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Vec d))).ae_tendsto_average_norm_sub hg]
    with x hx
  have havg : Tendsto
      (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖g y - g x‖ ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact ((hx.comp (Besicovitch.tendsto_filterAt volume x)).comp
      (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝[>] 0)))
  simp only [MeasureTheory.convolution_eq_swap, ContinuousLinearMap.lsmul_apply] at havg ⊢
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (C₀ * V) havg
  · filter_upwards with δ
    exact hg.integrableOn_isCompact (isCompact_closedBall x δ)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hpres : MeasurePreserving (fun y : Vec d => x - y)
        (volume : Measure (Vec d)) volume :=
      Measure.measurePreserving_sub_left volume x
    have hchange := hpres.integral_comp
      (Homeomorph.subLeft x).measurableEmbedding (harmonicKernelScaled δ)
    rw [hchange, harmonicKernelScaled_integral_eq_one hδ]
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro y hy
    have hk : harmonicKernelScaled δ (x - y) ≠ 0 :=
      Function.mem_support.mp hy
    have hts : x - y ∈ tsupport (harmonicKernelScaled δ) :=
      subset_tsupport _ (Function.mem_support.mpr hk)
    have heuc : x - y ∈ euclideanBall (0 : Vec d) δ :=
      (harmonicKernelScaled_tsupport_subset hδ) hts
    have hmetric : x - y ∈ Metric.ball (0 : Vec d) δ :=
      euclideanBall_subset_supBall hδ heuc
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖x - y‖ < δ := by
      simpa [Metric.mem_ball, dist_zero_right] using hmetric
    simpa [norm_sub_rev] using hnorm.le
  · filter_upwards [self_mem_nhdsWithin] with δ hδ y
    have hbound : |harmonicKernelScaled δ (x - y)| ≤ δ⁻¹ ^ d * C₀ := by
      rw [harmonicKernelScaled, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) _)]
      simpa only [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (hC₀ (δ⁻¹ • (x - y)))
          (pow_nonneg (inv_nonneg.mpr hδ.le) d)
    change |harmonicKernelScaled δ (x - y)| ≤
      C₀ * V / (volume (Metric.closedBall x δ)).toReal
    rw [hvolume x hδ]
    have hδpow : 0 < δ ^ d := pow_pos hδ _
    have hvol : 0 < δ ^ d * V := mul_pos hδpow hVpos
    calc
      |harmonicKernelScaled δ (x - y)| ≤ δ⁻¹ ^ d * C₀ := hbound
      _ = (C₀ * V) / (δ ^ d * V) := by
        rw [inv_pow]
        field_simp

end

end PDE
