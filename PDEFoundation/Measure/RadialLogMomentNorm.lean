module

public import PDEFoundation.Measure.EuclideanRadialLogMoment
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-! # Exact normalized `Lᵖ` norm of the radial logarithm -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem measurable_neg_log_vecEuclideanNorm_div {d : ℕ} {R : ℝ} (hR : 0 < R) :
    Measurable (fun x : Vec d => -Real.log (vecEuclideanNorm x / R)) := by
  apply Measurable.neg
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  exact (ContinuousAt.log
    (continuous_vecEuclideanNorm.continuousAt.div_const R)
    (div_ne_zero (vecEuclideanNorm_pos_iff.mpr hx0).ne' hR.ne')).continuousWithinAt

/-- The negative logarithmic radius has its exact normalized finite-exponent
norm on every positive-radius native round ball. -/
theorem memLp_and_toReal_eLpNorm_neg_log_vecEuclideanNorm_div
    {d : ℕ} (hd : 0 < d) {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    let t : Vec d → ℝ := fun x => -Real.log (vecEuclideanNorm x / R)
    MemLp t (ENNReal.ofReal p) (normalizedVolumeOn (euclideanBall 0 R)) ∧
      (eLpNorm t (ENNReal.ofReal p)
        (normalizedVolumeOn (euclideanBall 0 R))).toReal =
        Real.Gamma (p + 1) ^ (1 / p) / (d : ℝ) := by
  let B := euclideanBall (0 : Vec d) R
  let μ := normalizedVolumeOn B
  let t : Vec d → ℝ := fun x => -Real.log (vecEuclideanNorm x / R)
  have hraw : IntegrableOn (fun x => t x ^ p) B := by
    simpa only [B, t] using
      integrableOn_neg_log_vecEuclideanNorm_div_euclideanBall hd hR hp
  have hmoment : Integrable (fun x => t x ^ p) μ := by
    exact hraw.smul_measure (ENNReal.inv_ne_top.mpr
      (ne_of_gt (volume_euclideanBall_pos (0 : Vec d) hR)))
  have htNonnegRaw : ∀ᵐ x ∂volume.restrict B, 0 ≤ t x := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_euclideanBall (0 : Vec d) R)] with x hx
    by_cases hx0 : x = 0
    · subst x
      simp [t, vecEuclideanNorm, vecNormSq, vecDot]
    · have hnorm : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx0
      have hlt : vecEuclideanNorm x < R := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hx
        simpa only [sub_zero] using hx
      dsimp only [t]
      exact neg_nonneg.mpr (Real.log_nonpos (div_nonneg hnorm.le hR.le)
        (div_le_one hR |>.mpr hlt.le))
  have htNonneg : ∀ᵐ x ∂μ, 0 ≤ t x := by
    apply htNonnegRaw.filter_mono
    apply Measure.AbsolutelyContinuous.ae_le
    dsimp only [μ, normalizedVolumeOn]
    exact Measure.smul_absolutelyContinuous
  have hnormMoment : Integrable (fun x => ‖t x‖ ^ p) μ := by
    apply hmoment.congr
    filter_upwards [htNonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  have hAES : AEStronglyMeasurable t μ :=
    (measurable_neg_log_vecEuclideanNorm_div hR).aestronglyMeasurable
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp
  have hpTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htLp : MemLp t (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff hAES hp0 hpTop]
    simpa only [ENNReal.toReal_ofReal hp.le] using hnormMoment
  refine ⟨htLp, ?_⟩
  rw [toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp htLp]
  have hIntegral : (∫ x, ‖t x‖ ^ p ∂μ) =
      Real.Gamma (p + 1) / (d : ℝ) ^ p := by
    have hnormAE : (fun x => ‖t x‖ ^ p) =ᵐ[μ] (fun x => t x ^ p) := by
      filter_upwards [htNonneg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx]
    rw [integral_congr_ae hnormAE]
    simpa only [μ, B, t, integral_normalizedVolumeOn_eq_integralAverage] using
      integralAverage_neg_log_vecEuclideanNorm_div_euclideanBall hd hR hp
  rw [hIntegral]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hGamma : 0 < Real.Gamma (p + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  rw [Real.div_rpow hGamma.le (Real.rpow_nonneg hdR.le p)]
  have hden : ((d : ℝ) ^ p) ^ (1 / p) = (d : ℝ) := by
    rw [← Real.rpow_mul hdR.le]
    have : p * (1 / p : ℝ) = 1 := by field_simp [hp.ne']
    rw [this, Real.rpow_one]
  rw [hden]

end
end PDE
