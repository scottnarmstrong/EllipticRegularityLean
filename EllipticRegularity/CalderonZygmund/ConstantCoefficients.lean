module

public import CZStatements.General

@[expose] public section

open scoped ENNReal

namespace PDE

noncomputable section

open MeasureTheory

/-- For a constant elliptic coefficient, the oscillation condition is automatic.
One constant works for every finite exponent and all coefficient matrices and data. -/
theorem exists_calderonZygmund_constant_coefficients
    (d : ℕ) (hd : 0 < d) (Lambda : ℝ) (hLambda : 1 ≤ Lambda) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 2 ≤ p →
      ∀ (A : Mat d), IsEllipticMatrix 1 Lambda A →
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1))
        (F : Vec d → Vec d),
      (∀ i : Fin d,
        AEStronglyMeasurable (fun x => F x i)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1))),
      IsWeakDivergenceFormSolutionOn (fun _ => A)
          (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) F →
      MemW1p (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          euclideanFieldLpMeanNormOn
              (euclideanBall (0 : Vec d) (1 / 2 : ℝ))
              (ENNReal.ofReal p) u.grad
              (memLp_normalizedVolumeOn_of_memLpOn hgrad
                (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C *
              (Real.sqrt
                  (integralAverage (euclideanBall (0 : Vec d) 1)
                    (fun x => vecNormSq (u.grad x))) +
                p * euclideanFieldLpMeanNormOn
                  (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) F
                  (memLp_normalizedVolumeOn_of_memLpOn hF
                    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨C, hC, hCZ⟩ := exists_calderonZygmund d hd Lambda hLambda
  refine ⟨C, hC, ?_⟩
  intro p hp A hA u F hFcoord hF hsol
  let W := euclideanBall (0 : Vec d) 1
  have hWpos : 0 < volume W := volume_euclideanBall_pos _ (by norm_num)
  have hWtop : volume W < ⊤ := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  let : IsProbabilityMeasure (normalizedVolumeOn W) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hWpos hWtop
  have hMean : (fun i j => integralAverage W (fun _ : Vec d => A i j)) = A := by
    funext i j
    rw [← integral_normalizedVolumeOn_eq_integralAverage]
    simp
  have hClose : ∀ᵐ x ∂volumeOn W,
      IsMatrixPerturbationLE (1 / (C * p)) A
        (fun i j => integralAverage W (fun _ : Vec d => A i j)) := by
    rw [hMean]
    filter_upwards with x
    intro xi
    have hdelta : 0 ≤ 1 / (C * p) := by positivity
    simpa only [sub_self, matVecMul, Matrix.zero_apply,
      vecEuclideanNorm, vecNormSq, vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      Real.sqrt_zero] using mul_nonneg hdelta (vecEuclideanNorm_nonneg xi)
  exact hCZ p hp (fun _ => A) (fun _ _ => measurable_const.aemeasurable)
    (Filter.Eventually.of_forall fun _ => hA) hClose u F hFcoord hF hsol

end
end PDE
