module

public import PDEFoundation.Ambient.MatAppendEllipticity
public import PDEFoundation.Analysis.ClassicalDivergencePointRemoval
public import PDEFoundation.Analysis.RadialLogDivergence
public import PDEFoundation.Analysis.RadialModeGradient
public import PDEFoundation.Analysis.RadialModeSmooth
public import PDEFoundation.Measure.EuclideanFieldMeanLp
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Measure.PlanarRadialLogEnergy
public import PDEFoundation.Measure.RadialLogMeanLowerBound
public import PDEFoundation.Measure.RadialLogUnbounded
public import PDEFoundation.Measure.VecAppendBallNormComparison
public import PDEFoundation.Measure.VecAppendBallNonLp
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakDivergenceFormProductLift
public import PDEFoundation.Sobolev.PuncturedClassicalWeakGradient
public import EllipticRegularity.CalderonZygmund.ForcingAsymptotic
public import CZStatements.ForcingSharpness

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The literal logarithmic solution rules out every sublinear coefficient in
front of the normalized forcing norm when the energy coefficient is fixed. -/
theorem exists_logarithmic_forcing_violation
    (A : ℝ) (hA : 0 ≤ A) (b : ℝ → ℝ)
    (hb : Filter.Tendsto (fun p : ℝ => b p / p) Filter.atTop (nhds 0))
    (hb_nonneg : ∀ p : ℝ, 2 ≤ p → 0 ≤ b p) :
    let B := euclideanBall (0 : Vec 2) 1
    let V := euclideanBall (0 : Vec 2) (1 / 2 : ℝ)
    ∃ u : H1Function B,
      (∀ x, u.toFun x = x 0 * Real.log (vecEuclideanNorm x)) ∧
      (∀ x i, u.grad x i = basisVec 0 i * Real.log (vecEuclideanNorm x) +
        x 0 * x i / vecNormSq x) ∧
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 2)) B u 0 (radialForcing 0) ∧
      MemLp (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ∧
      eLpNorm (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤ (volumeOn B) ≤ 2 ∧
      Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) =
        Real.sqrt (1 / 2 : ℝ) ∧
      ∃ p : ℝ, 2 ≤ p ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p) (volumeOn V),
          ∃ hforce : MemLp (fun x => vecEuclideanNorm (radialForcing 0 x))
              (ENNReal.ofReal p) (volumeOn B),
            A * Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) +
                b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p)
                  (radialForcing 0)
                  (memLp_normalizedVolumeOn_of_memLpOn hforce
                    (volume_euclideanBall_pos (0 : Vec 2) (by norm_num))) <
              euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
                (memLp_normalizedVolumeOn_of_memLpOn hgrad
                  (volume_euclideanBall_pos (0 : Vec 2) (by norm_num))) := by
  let B := euclideanBall (0 : Vec 2) 1
  let V := euclideanBall (0 : Vec 2) (1 / 2 : ℝ)
  rcases exists_planar_logarithmic_forcing_sharpness with
    ⟨u, hu, hgradFormula, hFcoord, hFtop, hFtopNorm, hsol, henergy,
      hgradLower, hunbounded⟩
  have hnot := not_forall_half_Gamma_le_constant_add_sublinear
    (A * Real.sqrt (1 / 2 : ℝ)) b hb
  push Not at hnot
  obtain ⟨p, hp, hpStrict⟩ := hnot
  obtain ⟨hgrad, hgradBound⟩ := hgradLower p hp
  have hBPos : 0 < volume B := by
    simpa only [B] using
      volume_euclideanBall_pos (0 : Vec 2) (by norm_num : (0 : ℝ) < 1)
  have hBTop : volume B < ∞ := by
    simpa only [B] using lt_top_iff_ne_top.mpr
      (volume_euclideanBall_ne_top (0 : Vec 2) (by norm_num : (0 : ℝ) ≤ 1))
  obtain ⟨hforce, hforceMono⟩ :=
    exists_memLp_vecEuclideanNorm_of_exponent_le_and_lpMeanNorm_le
      (U := B) (q := ENNReal.ofReal p) (p := ⊤) le_top hBPos hBTop
      (radialForcing 0) hFtop
  have hFtopMean := memLp_normalizedVolumeOn_of_memLpOn hFtop hBPos
  have hFbound : ∀ᵐ x ∂normalizedVolumeOn B,
      ‖vecEuclideanNorm (radialForcing 0 x)‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
    exact vecEuclideanNorm_radialForcing_le_two 0 x
  have hFmeanTopLe :
      euclideanFieldLpMeanNormOn B ⊤ (radialForcing 0) hFtopMean ≤ 2 := by
    rw [euclideanFieldLpMeanNormOn, lpMeanNormOn_eq_toReal]
    change (eLpNorm (fun x => vecEuclideanNorm (radialForcing 0 x)) ⊤
      (normalizedVolumeOn B)).toReal ≤ 2
    rw [eLpNorm_exponent_top hFtopMean.aestronglyMeasurable]
    calc
      (eLpNormEssSup (fun x => vecEuclideanNorm (radialForcing 0 x))
          (normalizedVolumeOn B)).toReal ≤ (ENNReal.ofReal 2).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (eLpNormEssSup_le_of_ae_bound hFbound)
      _ = 2 := by norm_num
  have hFmeanLe :
      euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) (radialForcing 0)
          (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤ 2 :=
    hforceMono.trans hFmeanTopLe
  have hb0 : 0 ≤ b p := hb_nonneg p hp
  have hforcingTerm :
      b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) (radialForcing 0)
          (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤ 2 * b p := by
    calc
      b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) (radialForcing 0)
          (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤ b p * 2 :=
        mul_le_mul_of_nonneg_left hFmeanLe hb0
      _ = 2 * b p := by ring
  have henergyNonneg :
      0 ≤ A * Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) :=
    mul_nonneg hA (Real.sqrt_nonneg _)
  refine ⟨u, hu, hgradFormula, hsol, hFtop, hFtopNorm, henergy,
    p, hp, hgrad, hforce, ?_⟩
  calc
    A * Real.sqrt (integralAverage B (fun x => vecNormSq (u.grad x))) +
          b p * euclideanFieldLpMeanNormOn B (ENNReal.ofReal p) (radialForcing 0)
            (memLp_normalizedVolumeOn_of_memLpOn hforce hBPos) ≤
        A * Real.sqrt (1 / 2 : ℝ) + 2 * b p := by
      rw [henergy]
      exact add_le_add le_rfl hforcingTerm
    _ < (1 / 2 : ℝ) * Real.rpow (Real.Gamma (p + 1)) (1 / p) - 1 := by
      linarith only [hpStrict, henergyNonneg]
    _ ≤ euclideanFieldLpMeanNormOn V (ENNReal.ofReal p) u.grad
          (memLp_normalizedVolumeOn_of_memLpOn hgrad
            (volume_euclideanBall_pos (0 : Vec 2) (by norm_num))) :=
      hgradBound

end

end PDE
