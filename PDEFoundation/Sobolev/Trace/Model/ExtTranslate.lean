module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Continuity of translations in `L^p`

For `f ∈ L^q(μ)` (`μ` an additive Haar measure on a finite-dimensional real normed space,
`1 ≤ q < ∞`) the translates `f(· + v)` converge to `f` in `L^q` as `v → 0`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

section Translate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eLpNorm_translate_eq {q : ℝ≥0∞} {f : E → ℝ} (hf : AEStronglyMeasurable f μ) (v : E) :
    eLpNorm (fun z => f (z + v)) q μ = eLpNorm f q μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right μ v)

theorem exists_nnreal_mul_le {M : ℝ≥0∞} (hM : M ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : NNReal, 0 < δ ∧ (δ : ℝ≥0∞) * M ≤ ε := by
  by_cases hεt : ε = ⊤
  · exact ⟨1, one_pos, by simp [hεt]⟩
  · lift ε to NNReal using hεt
    lift M to NNReal using hM
    refine ⟨ε / (M + 1), ?_, ?_⟩
    · have : (0 : NNReal) < ε := by exact_mod_cast hε
      positivity
    · rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      gcongr
      exact le_self_add

theorem tendsto_eLpNorm_translate_of_continuous {q : ℝ≥0∞} {h : E → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto (fun v : E => eLpNorm (fun z => h (z + v) - h z) q μ) (𝓝 0) (𝓝 0) := by
  have huc : UniformContinuous h := hs.uniformContinuous_of_continuous hc
  obtain ⟨R, hR⟩ := hs.isBounded.subset_closedBall (0 : E)
  have hK : IsCompact (Metric.closedBall (0 : E) (R + 1)) := isCompact_closedBall _ _
  set K := Metric.closedBall (0 : E) (R + 1) with hKdef
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set M : ℝ≥0∞ := (μ.restrict K) Set.univ ^ q.toReal⁻¹ with hM
  have hMfin : M ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hK.measure_lt_top.ne
  obtain ⟨δ, hδ0, hδ⟩ := exists_nnreal_mul_le hMfin hε
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuous_iff.1 huc δ (by exact_mod_cast hδ0)
  have hnhds : Metric.ball (0 : E) (min η 1) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ (lt_min hη0 one_pos)
  filter_upwards [hnhds] with v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  have hv1 : ‖v‖ < η := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < 1 := lt_of_lt_of_le hv (min_le_right _ _)
  have hcont : Continuous fun z => h (z + v) - h z := (hc.comp (continuous_id.add continuous_const)).sub hc
  have hsupp : Function.support (fun z => h (z + v) - h z) ⊆ K := by
    intro z hz
    by_contra hzK
    apply hz
    have h1 : R + 1 < ‖z‖ := by simpa [hKdef] using hzK
    have h2 : h z = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have h3 : h (z + v) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      have := norm_sub_norm_le z (-v)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    simp [h2, h3]
  calc eLpNorm (fun z => h (z + v) - h z) q μ
      = eLpNorm (fun z => h (z + v) - h z) q (μ.restrict K) :=
        (eLpNorm_restrict_eq_of_support_subset hcont.aestronglyMeasurable hsupp).symm
    _ ≤ δ • M := by
        refine eLpNorm_le_of_ae_nnnorm_bound hcont.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => ?_)
        have := hη (a := z + v) (b := z) (by simpa using hv1)
        rw [Real.dist_eq] at this
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
        exact this.le
    _ = (δ : ℝ≥0∞) * M := by rw [ENNReal.smul_def, smul_eq_mul]
    _ ≤ ε := hδ

theorem tendsto_eLpNorm_translate {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqt : q ≠ ⊤) {f : E → ℝ}
    (hf : MemLp f q μ) :
    Tendsto (fun v : E => eLpNorm (fun z => f (z + v) - f z) q μ) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨h, hhs, hhn, hhc, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hqt hε3.ne'
  have ht := tendsto_eLpNorm_translate_of_continuous μ (q := q) hhc hhs
  rw [ENNReal.tendsto_nhds_zero] at ht
  filter_upwards [ht (ε / 3) hε3] with v hv
  have hmeas : AEStronglyMeasurable (f - h) μ := hf.aestronglyMeasurable.sub hhc.aestronglyMeasurable
  have key : (fun z => f (z + v) - f z) =
      ((fun z => (f - h) (z + v)) + (fun z => h (z + v) - h z)) - (f - h) := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  calc eLpNorm (fun z => f (z + v) - f z) q μ
      = eLpNorm (((fun z => (f - h) (z + v)) + (fun z => h (z + v) - h z)) - (f - h)) q μ := by
        rw [key]
    _ ≤ eLpNorm ((fun z => (f - h) (z + v)) + (fun z => h (z + v) - h z)) q μ +
          eLpNorm (f - h) q μ := eLpNorm_sub_le hq1
    _ ≤ (eLpNorm (fun z => (f - h) (z + v)) q μ + eLpNorm (fun z => h (z + v) - h z) q μ) +
          eLpNorm (f - h) q μ := by
        gcongr
        exact eLpNorm_add_le hq1
    _ = eLpNorm (f - h) q μ + eLpNorm (fun z => h (z + v) - h z) q μ +
          eLpNorm (f - h) q μ := by
        rw [eLpNorm_translate_eq μ hmeas]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem lintegral_ofReal_abs_rpow_eq {p : ℝ} (hp : 0 < p) {F : E → ℝ}
    (hF : AEStronglyMeasurable F μ) :
    ∫⁻ z, ENNReal.ofReal (|F z| ^ p) ∂μ = eLpNorm F (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top hF,
    ENNReal.toReal_ofReal hp.le, ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

theorem tendsto_lintegral_translate {p : ℝ} (hp : 1 ≤ p) {f : E → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    Tendsto (fun v : E => ∫⁻ z, ENNReal.ofReal (|f (z + v) - f z| ^ p) ∂μ) (𝓝 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have h2 := tendsto_eLpNorm_translate μ h1 ENNReal.ofReal_ne_top hf
  have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
  rw [ENNReal.zero_rpow_of_pos hp0] at h3
  refine h3.congr fun v => ?_
  simp only [Function.comp]
  have hm : AEStronglyMeasurable (fun z => f (z + v) - f z) μ :=
    (hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_add_right μ v)).sub
      hf.aestronglyMeasurable
  rw [lintegral_ofReal_abs_rpow_eq μ hp0 hm]

end Translate

end PDE.TraceLane
