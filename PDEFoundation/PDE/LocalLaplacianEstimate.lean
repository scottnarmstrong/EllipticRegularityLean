module

public import PDEFoundation.PDE.LaplacianSparseForestLp
public import PDEFoundation.PDE.HarmonicComparisonZeroExtension
public import PDEFoundation.Measure.VectorForcingZeroExtension
public import PDEFoundation.Measure.FixedNormalizationBound
public import PDEFoundation.Measure.CalderonZygmundLocalNormFactors

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

/-- The local Laplacian estimate with constants chosen before the exponent,
the radii, the solution and the forcing. Both norms use the fixed unit-ball
volume normalization of the manuscript. -/
theorem exists_localLaplacianLp_constants (d : ℕ) (hd : 0 < d) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ (p : ℝ), 4 ≤ p → ∀ (s t : ℝ), 0 < s → s < t → t ≤ 1 →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) t)) (G : Vec d → Vec d),
      (∀ i, AEStronglyMeasurable (fun x => G x i)
        (volumeOn (euclideanBall (0 : Vec d) t))) →
      MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) t)) →
      IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d))
        (euclideanBall (0 : Vec d) t) u 0 G →
      MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) s)) ∧
      eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
            volumeOn (euclideanBall (0 : Vec d) s)) ≤
        ENNReal.ofReal (A * (t - s) ^ (-(d : ℝ) / 2) *
          Real.sqrt ((∫ x in euclideanBall (0 : Vec d) t, vecNormSq (u.grad x)) /
            (volume (euclideanBall (0 : Vec d) 1)).toReal)) +
        ENNReal.ofReal (K * p) *
          eLpNorm (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p)
            ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
              volumeOn (euclideanBall (0 : Vec d) t)) := by
  let C := (2 : ℝ) ^ (1 + (d : ℝ) / 2)
  let D := Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
    (Real.sqrt d / 2) ^ d)
  let κ := ((d : ℝ) + 2) / 2 * (1 + 2 / (d : ℝ)) ^ ((d : ℝ) / 2)
  let E := (1 + 2 * C) * D * Real.sqrt ((2 : ℝ) ^ d)
  let B := C * D * κ
  let M := 2 * (3 : ℝ) ^ ((d : ℝ) / 4)
  let A := E * (2 : ℝ) ^ ((d : ℝ) / 2)
  let K := B * (4 / 3 : ℝ) * M
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hB : 0 ≤ B := by dsimp only [B, C, D, κ]; positivity
  refine ⟨A, K, ?_, ?_, ?_⟩
  · dsimp only [A, E, C, D]; positivity
  · dsimp only [K, M]; positivity
  intro p hp s t hs hst ht1 u G hGcoord hGp hsol
  let Bt := euclideanBall (0 : Vec d) t
  let Bs := euclideanBall (0 : Vec d) s
  let F := Bt.indicator G
  have hBt : MeasurableSet Bt := (isOpen_euclideanBall _ _).measurableSet
  have hFcoord : ∀ i, AEStronglyMeasurable (fun x => F x i) volume :=
    fun i => aestronglyMeasurable_indicator_coordinate hBt G i (hGcoord i)
  have hFp : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume :=
    memLp_vecEuclideanNorm_indicator hBt G hGp
  have hsolF : IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) Bt u 0 F :=
    hsol.of_ae_eq_forcing (euclideanBall_indicator_ae_eq_forcing G (0 : Vec d) t)
  obtain ⟨hgrad, hraw⟩ := memLp_grad_and_eLpNorm_le_laplacian_sparseForest
    hd hs hst u F hFcoord hp hFp hsolF
  let U := Real.sqrt ((∫ x in Bt, vecNormSq (u.grad x)) /
    (volume (euclideanBall (0 : Vec d) 1)).toReal)
  have hAeq : (E * Real.sqrt ((2 / (t - s)) ^ d)) * U =
      A * (t - s) ^ (-(d : ℝ) / 2) * U := by
    rw [sqrt_two_div_pow_eq d (sub_pos.mpr hst)]
    dsimp only [A]
    ring
  have hKeq : K * p = B * ((4 / 3 : ℝ) * p) * M := by
    dsimp only [K]
    ring
  have hcoeff : ENNReal.ofReal (K * p) =
      ENNReal.ofReal B * (ENNReal.ofReal ((4 / 3 : ℝ) * p) * ENNReal.ofReal M) := by
    rw [hKeq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB]
    rw [mul_assoc]
  change eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn Bs) ≤ ENNReal.ofReal ((E * Real.sqrt ((2 / (t - s)) ^ d)) * U) *
        (volume Bs) ^ (1 / p) + ENNReal.ofReal B *
        (ENNReal.ofReal ((4 / 3 : ℝ) * p) *
          (ENNReal.ofReal M * eLpNorm (fun x => vecEuclideanNorm (F x))
            (ENNReal.ofReal p) volume)) at hraw
  rw [hAeq] at hraw
  have hraw' : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn Bs) ≤
      ENNReal.ofReal (A * (t - s) ^ (-(d : ℝ) / 2) * U) *
        ((volumeOn Bs) Set.univ) ^ (1 / p) +
      ENNReal.ofReal (K * p) *
        eLpNorm (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) (volumeOn Bt) := by
    rw [hcoeff, mul_assoc]
    rw [← eLpNorm_vecEuclideanNorm_indicator hBt G]
    simpa only [Bt, Bs, volumeOn, Measure.restrict_apply_univ, mul_assoc, F] using hraw
  have hmass : (volumeOn Bs) Set.univ ≤ volume (euclideanBall (0 : Vec d) 1) := by
    rw [volumeOn, Measure.restrict_apply_univ]
    exact measure_mono (euclideanBall_mono hs.le (hst.le.trans ht1))
  have hnorm := eLpNorm_fixedNormalization_le_of_raw_bound
    (volumeOn Bs) (volumeOn Bt) (fun x => vecEuclideanNorm (u.grad x))
    (fun x => vecEuclideanNorm (G x))
    (volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)) hmass
    (by linarith : 0 < p) _ _ hraw'
  exact ⟨hgrad, hnorm⟩

end PDE
