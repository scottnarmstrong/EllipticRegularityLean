module

public import PDEFoundation.Analysis.HilbertSubmean
public import PDEFoundation.Analysis.RadialAverage

/-! # Internal exact monotonicity of normalized Hilbert ball averages -/

@[expose] public section

namespace PDE.Internal

open MeasureTheory Metric Set InnerProductSpace
open scoped Laplacian

noncomputable section

variable {d : ℕ}

local notation "𝔼" => HilbertVec d

theorem integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage [NeZero d]
    {u : 𝔼 → ℝ} (hu : Continuous u) (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    ∫ y in Metric.ball x r, u y =
      (sphereMeasure d).real Set.univ *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
  classical
  set G : 𝔼 → ℝ :=
    fun z ↦ Set.indicator (Metric.ball (0 : 𝔼) r) (fun w ↦ u (x + w)) z with hG
  have hGint : Integrable G := by
    rw [hG]
    exact ((hu.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : 𝔼) r) |>.mono_set Metric.ball_subset_closedBall)
        |>.integrable_indicator measurableSet_ball
  have htrans : ∫ z, G z = ∫ y in Metric.ball x r, u y := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 ↦ Set.indicator (Metric.ball x r) u y) x
    have hfun : (fun y : 𝔼 ↦ Set.indicator (Metric.ball x r) u (x + y)) = G := by
      funext y
      change Set.indicator (Metric.ball x r) u (x + y) =
        Set.indicator (Metric.ball 0 r) (fun w ↦ u (x + w)) y
      by_cases hy : y ∈ Metric.ball 0 r
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem]
        simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero]
          using hy
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
        simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero]
          using hy
    rw [hfun] at h
    simpa only [MeasureTheory.integral_indicator measurableSet_ball] using h
  have hpolar := integral_eq_integral_Ioi_sphere (G := G) hGint
  have hinner : ∀ s ∈ Set.Ioi (0 : ℝ),
      ∫ ω, G (s • (ω : 𝔼)) ∂(sphereMeasure d) =
        Set.indicator (Set.Iio r)
          (fun t ↦ (sphereMeasure d).real Set.univ * sphereAverage x t u) s := by
    intro s hs
    by_cases hsr : s < r
    · rw [Set.indicator_of_mem (show s ∈ Set.Iio r from hsr)]
      have hmem : ∀ ω : Metric.sphere (0 : 𝔼) 1,
          s • (ω : 𝔼) ∈ Metric.ball 0 r := by
        intro ω
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, mem_sphere_zero_iff_norm.mp ω.2, mul_one]
        exact hsr
      have hfun : (fun ω : Metric.sphere (0 : 𝔼) 1 ↦ G (s • (ω : 𝔼))) =
          fun ω : Metric.sphere (0 : 𝔼) 1 ↦ u (x + s • (ω : 𝔼)) := by
        funext ω
        change Set.indicator (Metric.ball 0 r) (fun w ↦ u (x + w)) (s • (ω : 𝔼)) = _
        rw [Set.indicator_of_mem (hmem ω)]
      rw [hfun, integral_sphere_eq_measureReal_smul_sphereAverage, smul_eq_mul]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Iio r from hsr)]
      have hnotmem : ∀ ω : Metric.sphere (0 : 𝔼) 1,
          s • (ω : 𝔼) ∉ Metric.ball 0 r := by
        intro ω hmem
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs, mem_sphere_zero_iff_norm.mp ω.2, mul_one] at hmem
        exact hsr hmem
      simp only [hG, Set.indicator_of_notMem (hnotmem _), integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ by rw [hinner s hs])] at hpolar
  have hcollapse :
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ (d - 1) • Set.indicator (Set.Iio r)
          (fun t ↦ (sphereMeasure d).real Set.univ * sphereAverage x t u) s =
      (sphereMeasure d).real Set.univ *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
    rw [intervalIntegral.integral_of_le hr.le]
    rw [← integral_const_mul]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    have haene : ∀ᵐ s : ℝ ∂volume, s ≠ r := by simp [ae_iff, measure_singleton]
    filter_upwards [haene] with s hsrne
    by_cases hs0 : 0 < s
    · by_cases hsr : s < r
      · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 r from ⟨hs0, hsr.le⟩),
          Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs0),
          Set.indicator_of_mem (show s ∈ Set.Iio r from hsr), smul_eq_mul]
        ring
      · have hrs : r < s := lt_of_le_of_ne (le_of_not_gt hsr) (Ne.symm hsrne)
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 r from fun hmem ↦
              (not_lt_of_ge hmem.2) hrs),
          Set.indicator_of_mem (show s ∈ Set.Ioi 0 from hs0),
          Set.indicator_of_notMem (show s ∉ Set.Iio r from hsr)]
        simp
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 r from fun hmem ↦ hs0 hmem.1),
        Set.indicator_of_notMem (show s ∉ Set.Ioi 0 from hs0)]
  rw [hcollapse] at hpolar
  rw [← htrans, hpolar]

/-- The real volume of a Euclidean ball, expressed with the surface measure
normalization used by `sphereAverage`. -/
theorem volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div [NeZero d]
    (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal =
      (sphereMeasure d).real Set.univ * (r ^ d / d) := by
  have hpolar := integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage
    (d := d) (u := fun _ : 𝔼 ↦ (1 : ℝ)) continuous_const x hr
  simp only [integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hpolar
  simp_rw [sphereAverage_const] at hpolar
  simp only [mul_one] at hpolar
  rw [integral_pow] at hpolar
  simp only [zero_pow (NeZero.ne d), Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_sub
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)), Nat.cast_one, sub_zero] at hpolar
  simpa [Measure.real] using hpolar

/-- Polar representation of the volume-normalized average on a Euclidean
ball.  The sphere-area constant cancels exactly. -/
theorem normalizedIntegral_metricBall_eq_radialSphereAverage [NeZero d]
    {u : 𝔼 → ℝ} (hu : Continuous u) (x : 𝔼) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, u y =
      (d : ℝ) / r ^ d *
        ∫ s in (0 : ℝ)..r, s ^ (d - 1) * sphereAverage x s u := by
  rw [integral_metricBall_eq_sphereMeasure_mul_radialSphereAverage hu x hr,
    volume_metricBall_toReal_eq_sphereMeasure_mul_pow_div x hr]
  have hσ : (sphereMeasure d).real Set.univ ≠ 0 := sphereMeasure_real_univ_ne_zero
  have hrpow : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp

open scoped InnerProductSpace

/-- The volume-normalized ball average of a smooth subharmonic function is
nondecreasing with the radius.  This is the constant-one submean comparison
needed by the Schauder iteration. -/
theorem normalizedIntegral_metricBall_mono_of_laplacian_nonneg [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hlap : ∀ y ∈ Metric.ball x R, 0 ≤ Δ u y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    (volume (Metric.ball x a)).toReal⁻¹ * ∫ y in Metric.ball x a, u y ≤
      (volume (Metric.ball x b)).toReal⁻¹ * ∫ y in Metric.ball x b, u y := by
  rw [normalizedIntegral_metricBall_eq_radialSphereAverage hu.continuous x ha,
    normalizedIntegral_metricBall_eq_radialSphereAverage hu.continuous x
      (ha.trans_le hab)]
  apply normalized_radialIntegral_mono (continuous_sphereAverage hu.continuous x) ha hab
  intro s hs t ht hst
  exact sphereAverage_mono_of_laplacian_nonneg hu hlap hs.1 hst
    (ht.2.trans_lt hbR)

end

end PDE.Internal
