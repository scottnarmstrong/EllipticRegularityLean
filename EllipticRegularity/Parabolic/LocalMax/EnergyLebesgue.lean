/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakSlice.Ramp
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Smooth one-sided averages at Lebesgue points

For an integrable `g : ℝ → ℝ`, at almost every `t₁` the smooth one-sided averages
`∫ k_h(τ) g(τ) dτ`, with `k_h(τ) = h⁻¹ ρ((τ - (t₁ - h))/h)` and `ρ = rampDeriv`, converge to
`g t₁` as `h → 0+`.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology Metric PDE.Parabolic.WeakSlice

theorem rampDeriv_nonneg (x : ℝ) : 0 ≤ rampDeriv x :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem exists_rampDeriv_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ x, rampDeriv x ≤ c := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    rampDeriv_continuous.continuousOn
  refine ⟨|M|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have := hM x hx
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_abs_self M))
  · rw [rampDeriv_eq_zero_of_notMem hx]; exact abs_nonneg _

/-- The averaging kernel. -/
noncomputable def rampKernel (t₁ h τ : ℝ) : ℝ := h⁻¹ * rampDeriv ((τ - (t₁ - h)) / h)

theorem rampKernel_nonneg {t₁ h : ℝ} (hh : 0 < h) (τ : ℝ) : 0 ≤ rampKernel t₁ h τ :=
  mul_nonneg (inv_nonneg.2 hh.le) (rampDeriv_nonneg _)

theorem rampKernel_eq_zero {t₁ h τ : ℝ} (hh : 0 < h) (hτ : τ ∉ Icc (t₁ - h) t₁) :
    rampKernel t₁ h τ = 0 := by
  unfold rampKernel
  rw [rampDeriv_eq_zero_of_notMem, mul_zero]
  intro hx
  apply hτ
  obtain ⟨h0, h1⟩ := hx
  rw [le_div_iff₀ hh] at h0
  rw [div_le_iff₀ hh] at h1
  constructor <;> linarith

theorem rampKernel_continuous (t₁ h : ℝ) : Continuous (rampKernel t₁ h) := by
  unfold rampKernel
  exact continuous_const.mul (rampDeriv_continuous.comp (by fun_prop))

theorem rampKernel_integrable {t₁ h : ℝ} (hh : 0 < h) : Integrable (rampKernel t₁ h) :=
  ((rampKernel_continuous t₁ h).integrableOn_Icc (a := t₁ - h) (b := t₁)
    ).integrable_of_forall_notMem_eq_zero fun _ hτ => rampKernel_eq_zero hh hτ

theorem integral_rampKernel {t₁ h : ℝ} (hh : 0 < h) : ∫ τ, rampKernel t₁ h τ = 1 := by
  unfold rampKernel
  have h1 := integral_sub_right_eq_self (μ := volume)
    (fun τ : ℝ => h⁻¹ * rampDeriv (τ / h)) (t₁ - h)
  rw [h1, integral_const_mul, Measure.integral_comp_div, smul_eq_mul, abs_of_pos hh,
    integral_rampDeriv]
  field_simp

theorem Real_volume_closedBall_toReal (a r : ℝ) (hr : 0 ≤ r) :
    (volume (closedBall a r)).toReal = 2 * r := by
  rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]

/-- Key estimate: the smooth average differs from `g t₁` by at most `c` times the ball average. -/
theorem abs_integral_rampKernel_sub_le {g : ℝ → ℝ} (hg : Integrable g) {c : ℝ}
    (hc : ∀ x, rampDeriv x ≤ c) {t₁ h : ℝ} (hh : 0 < h) :
    |(∫ τ, rampKernel t₁ h τ * g τ) - g t₁| ≤
      c * ⨍ y in closedBall (t₁ - h / 2) (h / 2), ‖g y - g t₁‖ := by
  have hk := rampKernel_integrable (t₁ := t₁) hh
  have hkb : ∀ τ, rampKernel t₁ h τ ≤ h⁻¹ * c := fun τ =>
    mul_le_mul_of_nonneg_left (hc _) (inv_nonneg.2 hh.le)
  have hkg : Integrable (fun τ => rampKernel t₁ h τ * g τ) :=
    hg.bdd_mul (c := h⁻¹ * c) hk.aestronglyMeasurable (Eventually.of_forall fun τ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rampKernel_nonneg hh τ)]; exact hkb τ)
  have hc0 : 0 ≤ c := (rampDeriv_nonneg 0).trans (hc 0)
  have hdiff : (∫ τ, rampKernel t₁ h τ * g τ) - g t₁ =
      ∫ τ, rampKernel t₁ h τ * (g τ - g t₁) := by
    have : ∫ τ, rampKernel t₁ h τ * (g τ - g t₁) =
        (∫ τ, rampKernel t₁ h τ * g τ) - g t₁ * ∫ τ, rampKernel t₁ h τ := by
      rw [← integral_const_mul, ← integral_sub hkg (hk.const_mul _)]
      congr 1; ext τ; ring
    rw [this, integral_rampKernel hh, mul_one]
  rw [hdiff]
  set B := closedBall (t₁ - h / 2) (h / 2) with hB
  have hBeq : B = Icc (t₁ - h) t₁ := by
    rw [hB, Real.closedBall_eq_Icc]; congr 1 <;> ring
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hgi : IntegrableOn (fun y => ‖g y - g t₁‖) B :=
    (hg.integrableOn.sub (integrableOn_const (by
      rw [hB, Real.volume_closedBall]; exact ENNReal.ofReal_ne_top))).norm
  calc |∫ τ, rampKernel t₁ h τ * (g τ - g t₁)|
      = ‖∫ τ, rampKernel t₁ h τ * (g τ - g t₁)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ τ, ‖rampKernel t₁ h τ * (g τ - g t₁)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ, B.indicator (fun y => h⁻¹ * c * ‖g y - g t₁‖) τ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (Eventually.of_forall fun τ => ?_)
        · exact (integrable_indicator_iff hBm).2 (hgi.const_mul (h⁻¹ * c))
        · beta_reduce
          by_cases hτ : τ ∈ B
          · rw [indicator_of_mem hτ, norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (rampKernel_nonneg hh τ)]
            exact mul_le_mul_of_nonneg_right (hkb τ) (norm_nonneg _)
          · rw [indicator_of_notMem hτ, norm_mul, Real.norm_eq_abs, rampKernel_eq_zero hh
              (by rwa [hBeq] at hτ)]
            simp
    _ = h⁻¹ * c * ∫ y in B, ‖g y - g t₁‖ := by
        rw [integral_indicator hBm, integral_const_mul]
    _ = c * ⨍ y in B, ‖g y - g t₁‖ := by
        rw [setAverage_eq, smul_eq_mul, Measure.real, hB, Real_volume_closedBall_toReal _ _ (by linarith)]
        field_simp

/-- At almost every point, the smooth one-sided averages converge. -/
theorem ae_tendsto_rampKernel_integral {g : ℝ → ℝ} (hg : Integrable g) :
    ∀ᵐ t₁ : ℝ, Tendsto (fun h : ℝ => ∫ τ, rampKernel t₁ h τ * g τ) (𝓝[>] 0) (𝓝 (g t₁)) := by
  obtain ⟨c, -, hc⟩ := exists_rampDeriv_le
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure ℝ)) hg.locallyIntegrable 1] with t₁ ht
  have hδ : Tendsto (fun h : ℝ => h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun h : ℝ => h / 2) (𝓝 0) (𝓝 (0 / 2)) := (continuous_id.div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh using half_pos (mem_Ioi.1 hh)
  have havg := ht (ι := ℝ) (l := 𝓝[>] 0) (fun h => t₁ - h / 2) (fun h => h / 2) hδ
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      rw [mem_closedBall, Real.dist_eq]
      have hh' : (0 : ℝ) < h := hh
      rw [sub_sub_cancel, abs_of_nonneg (by linarith), one_mul])
  have hz : Tendsto (fun h : ℝ => c * ⨍ y in closedBall (t₁ - h / 2) (h / 2), ‖g y - g t₁‖)
      (𝓝[>] 0) (𝓝 0) := by simpa using havg.const_mul c
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hz
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [Real.norm_eq_abs]
  exact abs_integral_rampKernel_sub_le hg hc (t₁ := t₁) (mem_Ioi.1 hh)

end PDE.Parabolic.LocalMax
