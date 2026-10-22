module

public import PDEFoundation.PDE.PerturbativeBoundedGradient
public import PDEFoundation.Sobolev.H1.GradientLpUpgrade

@[expose] public section

namespace PDE
open MeasureTheory
open scoped _root_.ENNReal

/-- The high-exponent perturbative estimate under the temporary interior
gradient bound, including genuine Sobolev membership of the original function. -/
theorem exists_calderonZygmund_boundedGradient_highExponent
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : ℝ), 4 ≤ p →
    ∀ (a : CoeffField d),
    (∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE (1 / (C*p)) (a x) (1 : Mat d)) →
    ∀ (u : H1Function (euclideanBall (0 : Vec d) 1)) (F : Vec d → Vec d),
    (∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    ∀ (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1))),
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
    ∀ (M : ℝ), 0 ≤ M →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3/4)),
      vecEuclideanNorm (u.grad x) ≤ M) →
    MemW1p (euclideanBall (0 : Vec d) (1/2)) (ENNReal.ofReal p) u.toFun ∧
    ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1/2))),
    euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) (1/2))
      (ENNReal.ofReal p) u.grad
      (memLp_normalizedVolumeOn_of_memLpOn hgrad
        (volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
    C * (Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => vecNormSq (u.grad x))) +
      p * euclideanFieldLpMeanNormOn (euclideanBall (0 : Vec d) 1)
        (ENNReal.ofReal p) F
        (memLp_normalizedVolumeOn_of_memLpOn hF
          (volume_euclideanBall_pos (0 : Vec d) (by norm_num)))) := by
  obtain ⟨C, hC, hbound⟩ := exists_perturbativeLaplacian_boundedGradient_constants d hd
  refine ⟨C, hC, ?_⟩
  intro p hp a ha hclose u F hFcoord hF hsol M hM hgradBound
  have hδ : 0 ≤ 1 / (C*p) := by positivity
  obtain ⟨hgrad, hest⟩ := hbound p (1/(C*p)) M hp hδ hM a F u
    ha hclose hFcoord hF hsol hgradBound le_rfl
  have hsub : euclideanBall (0 : Vec d) (1/2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  let v := u.restrict (isOpen_euclideanBall _ _) hsub
  have hcoord : GradMemLpOn (euclideanBall (0 : Vec d) (1/2))
      (ENNReal.ofReal p) v.grad := by
    intro i
    apply hgrad.of_le ((v.gradMemL2 i).aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using!
      abs_apply_le_vecEuclideanNorm (u.grad x) i
  have hw := (v.toW1pOfGradMemLp hd
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by norm_num))
    (volume_euclideanBall_pos (0 : Vec d) (by norm_num)) p (by linarith) hcoord).memW1p
  refine ⟨hw, hgrad, ?_⟩
  exact hest

end PDE
