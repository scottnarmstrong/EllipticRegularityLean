module

public import PDEFoundation.Ambient.RadialLogFieldBounds
public import PDEFoundation.Measure.RadialLogMomentNorm
public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal

/-- A logarithmic coordinate gradient has a quantitative normalized finite
exponent lower bound on every round ball of radius at most one. -/
theorem exists_memLp_radialLogGradientField_and_lpMeanNorm_lower_bound
    {d : ℕ} (hd : 0 < d) (k : Fin d) {R p : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hp : 1 ≤ p) :
    ∃ hG : MemLp (fun x => vecEuclideanNorm (radialLogGradientField k x))
        (ENNReal.ofReal p) (volumeOn (euclideanBall 0 R)),
      Real.Gamma (p + 1) ^ (1 / p) / (d : ℝ) - 1 ≤
        euclideanFieldLpMeanNormOn (euclideanBall 0 R) (ENNReal.ofReal p)
          (radialLogGradientField k)
          (memLp_normalizedVolumeOn_of_memLpOn hG (volume_euclideanBall_pos 0 hR)) := by
  let B := euclideanBall (0 : Vec d) R
  let μ := normalizedVolumeOn B
  let g : Vec d → ℝ := fun x => vecEuclideanNorm (radialLogGradientField k x)
  let t : Vec d → ℝ := fun x => -Real.log (vecEuclideanNorm x / R)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hG : MemLp g (ENNReal.ofReal p) (volumeOn B) :=
    (memLp_vecEuclideanNorm_radialLogGradientField_unitBall hd k hp0).mono_measure
      (Measure.restrict_mono (euclideanBall_mono hR.le hR1) le_rfl)
  have hGM : MemLp g (ENNReal.ofReal p) μ :=
    memLp_normalizedVolumeOn_of_memLpOn hG (volume_euclideanBall_pos 0 hR)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      (volume_euclideanBall_pos 0 hR)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top 0 hR.le))
  have hOne : MemLp (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal p) μ := memLp_const 1
  have hSum := hGM.add hOne
  have hBM : ∀ᵐ x ∂μ, x ∈ B := by
    have hRaw : ∀ᵐ x ∂volume.restrict B, x ∈ B :=
      self_mem_ae_restrict (measurableSet_euclideanBall 0 R)
    apply hRaw.filter_mono
    exact Measure.AbsolutelyContinuous.ae_le Measure.smul_absolutelyContinuous
  have hPoint : ∀ᵐ x ∂μ, ‖t x‖ ≤ ‖g x + 1‖ := by
    filter_upwards [hBM] with x hx
    have hg : 0 ≤ g x := vecEuclideanNorm_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ g x + 1)]
    by_cases hx0 : x = 0
    · subst x
      simp [t, vecEuclideanNorm, vecNormSq, vecDot]
      linarith
    · have hr : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx0
      have hrR : vecEuclideanNorm x < R := by
        rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hx
        simpa only [sub_zero] using hx
      have hLogR : Real.log R ≤ 0 := Real.log_nonpos hR.le hR1
      have hLogr : Real.log (vecEuclideanNorm x) ≤ 0 :=
        Real.log_nonpos hr.le (hrR.le.trans hR1)
      have ht : 0 ≤ t x := by
        dsimp [t]
        exact neg_nonneg.mpr (Real.log_nonpos (div_nonneg hr.le hR.le)
          ((div_le_one hR).mpr hrR.le))
      rw [abs_of_nonneg ht]
      dsimp only [t]
      rw [Real.log_div hr.ne' hR.ne']
      have hb := (vecEuclideanNorm_radialLogGradientField_bounds k x).1
      rw [abs_of_nonpos hLogr] at hb
      change -Real.log (vecEuclideanNorm x) - 1 ≤ g x at hb
      linarith
  obtain ⟨htLp, htNorm⟩ := memLp_and_toReal_eLpNorm_neg_log_vecEuclideanNorm_div hd hR hp0
  have hMon : (eLpNorm t (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (fun x => g x + 1) (ENNReal.ofReal p) μ).toReal :=
    ENNReal.toReal_mono hSum.eLpNorm_ne_top (eLpNorm_mono_ae htLp.aestronglyMeasurable hPoint)
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hTri := eLpNorm_add_le (f := g) (g := fun _ : Vec d => (1 : ℝ)) (μ := μ) hpE
  have hTriR := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hGM.eLpNorm_ne_top, hOne.eLpNorm_ne_top⟩) hTri
  rw [ENNReal.toReal_add hGM.eLpNorm_ne_top hOne.eLpNorm_ne_top] at hTriR
  have hOneNorm : eLpNorm (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal p) μ = 1 := by
    rw [eLpNorm_const' 1 (by positivity) ENNReal.ofReal_ne_top]
    simp
  rw [hOneNorm] at hTriR
  refine ⟨hG, ?_⟩
  change Real.Gamma (p + 1) ^ (1 / p) / (d : ℝ) - 1 ≤
    (eLpNorm g (ENNReal.ofReal p) μ).toReal
  change (eLpNorm t (ENNReal.ofReal p) μ).toReal = _ at htNorm
  rw [htNorm] at hMon
  change (eLpNorm (fun x => g x + 1) (ENNReal.ofReal p) μ).toReal ≤
    (eLpNorm g (ENNReal.ofReal p) μ).toReal + 1 at hTriR
  linarith

end PDE
