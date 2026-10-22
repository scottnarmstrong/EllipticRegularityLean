module

public import PDEFoundation.PDE.PerturbativeRadiusRecurrence
public import PDEFoundation.Analysis.CalderonZygmundRadiusIteration

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

/-- The actual weak PDE and temporary interior gradient bound give the
perturbative high-exponent estimate in fixed unit-ball normalization. The
radius recurrence and its uniform bound are both discharged internally. -/
theorem exists_perturbativeLaplacian_fixedNorm_bound_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
    ∀ (p delta M : ℝ), 4 ≤ p → 0 ≤ delta → 0 ≤ M →
    ∀ (a : CoeffField d) (F : Vec d → Vec d)
      (u : H1Function (euclideanBall (0 : Vec d) 1)),
    (∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) →
    (∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)) →
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      vecEuclideanNorm (u.grad x) ≤ M) →
    K * p * delta ≤ 1 / 2 →
    (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
        volumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
    (A * (4 / (1 - calderonZygmundIterationSigma d)) ^ ((d : ℝ) / 2) /
      (1 - Real.sqrt 2 / 2)) *
      Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
        (fun x => vecNormSq (u.grad x))) +
    (2 * K) * p *
      (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))).toReal := by
  obtain ⟨A, K, hA, hK, hrec⟩ :=
    exists_perturbativeLaplacian_radiusRecurrence_constants d hd
  refine ⟨A, K, hA, hK, ?_⟩
  intro p delta M hp hdelta hM a F u ha hclose hFcoord hFp hsol hbound hη
  let Φ : ℝ → ℝ := fun r =>
    (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
        volumeOn (euclideanBall (0 : Vec d) r))).toReal
  let U := Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
    (fun x => vecNormSq (u.grad x)))
  let NF := (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
    (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))).toReal
  have hφBound : ∀ r, 1 / 2 ≤ r → r < 3 / 4 → Φ r ≤ M := by
    intro r hr ht
    have hnorm := (exists_uniform_interior_eLpNorm_of_ae_bound u
      (by linarith : 1 ≤ p) hM hbound r hr ht).2
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [Φ, ENNReal.toReal_ofReal hM] using hreal
  have hφRec : ∀ s t, 1 / 2 ≤ s → s < t → t < 3 / 4 →
      Φ s ≤ (A * U) * (t - s) ^ (-(d : ℝ) / 2) +
        (K * p * NF) + (K * p * delta) * Φ t := by
    intro s t hs hst ht
    have h := hrec p delta M hp hdelta hM a F u ha hclose hFcoord hFp
      hsol hbound s t hs hst ht
    dsimp only [Φ, U, NF]
    convert h using 1; ring
  have hresult := calderonZygmundRadiusIteration_bound hd Φ
    (A := A * U) (B := K * p * NF) (η := K * p * delta) (M := M)
    (mul_nonneg hA (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg hK (by linarith)) ENNReal.toReal_nonneg)
    (mul_nonneg (mul_nonneg hK (by linarith)) hdelta)
    hη hφBound hφRec
  dsimp only [Φ, U, NF] at hresult
  convert hresult using 1; ring

end PDE
