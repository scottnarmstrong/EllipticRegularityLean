module

public import EllipticRegularity.Schauder.Gradient
public import PDEFoundation.Measure.SchauderForcing

/-! # Interior gradient control from the actual critical forcing norm -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The gradient scale constant is chosen using dimension alone, before the
Hölder exponent, coefficients, solution, and forcing. All forcing scale
hypotheses of the dyadic iteration are discharged from the actual `L^p` data. -/
theorem exists_schauder_interior_gradient_constant
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {a : CoeffField d} (u : H1Function (euclideanBall (0 : Vec d) 1))
        {F : Vec d → Vec d},
      (∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
        IsMatrixPerturbationLE ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) (a x) 1) →
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal (schauderSourceExponent d α)) (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
        0 < r → r ≤ 1 / 2 → r ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x))) ≤
        C * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal (schauderSourceExponent d α)) F hF / (1 - α)) := by
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  let A : ℝ := D / Real.sqrt (volume (euclideanBall (0 : Vec d) (1 / 2))).toReal
  let B : ℝ := 8 * D ^ 2 * schauderForcingVolumePrice d
  have hA : 0 ≤ A := div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg D))
      (schauderForcingVolumePrice_pos d).le
  refine ⟨A + B + 1, by linarith, ?_⟩
  intro α hα0 hα1 a u F ha hclose hFcoord hF hsol z hz r hr hrhalf
  let N := euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
    (ENNReal.ofReal (schauderSourceExponent d α)) F hF
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hp := two_le_schauderSourceExponent hd hα0 hα1
  have hFL2 := memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm
    hp (0 : Vec d) (by norm_num : (0 : ℝ) < 1) (Set.Subset.refl _) hF hFcoord
  have hM : 0 ≤ schauderForcingVolumePrice d * N :=
    mul_nonneg (schauderForcingVolumePrice_pos d).le hN
  have hforce : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 → r ^ (1 - α) *
        Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (F x))) ≤
      schauderForcingVolumePrice d * N := by
    intro z hz r hr hrhalf
    apply schauder_forcing_euclideanBall_le_unitLp hd hα0 hα1 z hr
    exact (euclideanBall_mono hr.le hrhalf).trans
      (euclideanBall_half_subset_unit_of_center_mem_half hz)
  have hpre := schauder_interior_gradient_bound_of_forcing_scale
    (by omega : 0 < d) hα0 hα1
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith))
    le_rfl hM u ha hclose hFL2 hsol hforce z hz r hr hrhalf
  let G := Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x))
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hQ : 0 ≤ N / (1 - α) := div_nonneg hN (by linarith)
  have hpre' : r ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (u.grad x))) ≤
      A * G + B * (N / (1 - α)) := by
    convert hpre using 1
    dsimp only [A, B, D, G]
    ring
  change _ ≤ (A + B + 1) * (G + N / (1 - α))
  exact hpre'.trans (by nlinarith only [mul_nonneg hA hQ, mul_nonneg hB hG, hG, hQ])

end

end PDE
