module

public import PDEFoundation.Monotonicity.ACF.WeightedCutoff
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lebesgue points and the averaging kernel

For an integrable `f : ℝ → ℝ`, at almost every `r`, `∫ ker_{r,k} f → f r` as `k → 0⁺`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

theorem ae_tendsto_kernel_average {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ r : ℝ, Tendsto (fun k => ∫ ρ, acfKer r k ρ * f ρ) (𝓝[>] 0) (𝓝 (f r)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure ℝ)) hf.locallyIntegrable 1] with r hr
  have hlim : Tendsto (fun k : ℝ => ⨍ y in Metric.closedBall r k, ‖f y - f r‖) (𝓝[>] 0) (𝓝 0) :=
    hr (ι := ℝ) (l := 𝓝[>] (0 : ℝ)) (fun _ => r) (fun k => k) tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with k hk
      simp only [Metric.mem_closedBall, dist_self, one_mul]
      exact le_of_lt hk)
  obtain ⟨C, hC0, hC⟩ := exists_acfKer_bound
  -- the bound `‖∫ ker f - f r‖ ≤ 2 C ⨍ ‖f - f r‖`
  have hbound : ∀ k : ℝ, 0 < k → ‖(∫ ρ, acfKer r k ρ * f ρ) - f r‖ ≤
      2 * C * ⨍ y in Metric.closedBall r k, ‖f y - f r‖ := by
    intro k hk
    have hkerc : Continuous (acfKer r k) := continuous_acfKer
    have hsupp : ∀ ρ, ρ ∉ Icc r (r + k) → acfKer r k ρ = 0 := fun ρ hρ =>
      Function.notMem_support.mp (fun hh => hρ (acfKer_support_subset hk hh))
    have hkerint : Integrable (acfKer r k) :=
      hkerc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc hsupp)
    have hkf : Integrable (fun ρ => acfKer r k ρ * f ρ) :=
      Integrable.bdd_mul (c := C / k) hf hkerc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ρ => by simpa using hC r k ρ hk)
    have hmass := integral_acfKer (r := r) hk
    have hdiff : (∫ ρ, acfKer r k ρ * f ρ) - f r = ∫ ρ, acfKer r k ρ * (f ρ - f r) := by
      have : ∫ ρ, acfKer r k ρ * (f ρ - f r) =
          (∫ ρ, acfKer r k ρ * f ρ) - (∫ ρ, acfKer r k ρ) * f r := by
        simp only [mul_sub]
        rw [integral_sub hkf (hkerint.mul_const _), integral_mul_const]
      rw [this, hmass, one_mul]
    rw [hdiff]
    have hsupp2 : ∀ ρ, ρ ∉ Metric.closedBall r k → acfKer r k ρ * (f ρ - f r) = 0 := by
      intro ρ hρ
      rw [hsupp ρ (fun h => hρ (by
        rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
        constructor <;> linarith [h.1, h.2])), zero_mul]
    have hfr : IntegrableOn (fun y => ‖f y - f r‖) (Metric.closedBall r k) :=
      (hf.integrableOn.sub (integrableOn_const (by
        rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top))).norm
    have hkd : Integrable (fun ρ => acfKer r k ρ * (f ρ - f r)) := by
      have := hkf.sub (hkerint.mul_const (f r))
      refine this.congr (Filter.Eventually.of_forall fun ρ => ?_)
      simp only [Pi.sub_apply, mul_sub]
    calc ‖∫ ρ, acfKer r k ρ * (f ρ - f r)‖
        ≤ ∫ ρ, ‖acfKer r k ρ * (f ρ - f r)‖ := norm_integral_le_integral_norm _
      _ = ∫ ρ in Metric.closedBall r k, ‖acfKer r k ρ * (f ρ - f r)‖ := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ρ hρ => ?_).symm
          rw [hsupp2 ρ hρ, norm_zero]
      _ ≤ ∫ ρ in Metric.closedBall r k, (C / k) * ‖f ρ - f r‖ := by
          refine setIntegral_mono_on hkd.norm.integrableOn (hfr.const_mul _)
            Metric.isClosed_closedBall.measurableSet fun ρ _ => ?_
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (by simpa using hC r k ρ hk) (norm_nonneg _)
      _ = 2 * C * ⨍ y in Metric.closedBall r k, ‖f y - f r‖ := by
          rw [integral_const_mul, setAverage_eq, smul_eq_mul]
          have hvol : (volume : Measure ℝ).real (Metric.closedBall r k) = 2 * k := by
            rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]
          rw [hvol]
          field_simp
  have hsq : Tendsto (fun k : ℝ => 2 * C * ⨍ y in Metric.closedBall r k, ‖f y - f r‖)
      (𝓝[>] 0) (𝓝 0) := by simpa using hlim.const_mul (2 * C)
  have hdiff : Tendsto (fun k : ℝ => (∫ ρ, acfKer r k ρ * f ρ) - f r) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' (by filter_upwards [self_mem_nhdsWithin] with k hk using hbound k hk) hsq
  simpa using hdiff.add_const (f r)

end

end PDE
