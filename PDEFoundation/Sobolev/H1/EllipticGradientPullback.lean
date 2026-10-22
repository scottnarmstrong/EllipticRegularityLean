module

public import PDEFoundation.Sobolev.H1.EllipticOscillationPullback

/-!
# Gradient mean bounds from the elliptic pullback
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- On the inscribed ball of the elliptic image, multiplying the transformed
gradient by the normalizer recovers the original gradient pointwise. The same
identity transfers centered and uncentered mean bounds at every admissible
radius. -/
theorem ellipticNormalizer_restrictedGradient_mean_bounds
    {A : Mat d} {Lam R : ℝ} (hA : IsEllipticMatrix 1 Lam A)
    (hR : 0 < R) (z : Vec d) (u : H1Function (euclideanBall z R)) :
    let e := ellipticNormalizerContinuousLinearEquiv hA
    let T := ellipticNormalizer A
    let rho := R / Real.sqrt Lam
    let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _)
      (euclideanBall_subset_ellipticNormalizer_image hA hR z)
    (∀ x : Vec d, matVecMul T (v.grad (e x)) = u.grad x) ∧
      ∀ r : ℝ, 0 < r → r ≤ rho →
        centeredVectorMeanL2 (euclideanBall z r) u.grad ≤
            Real.sqrt ((Real.sqrt Lam) ^ d) *
              centeredVectorMeanL2 (euclideanBall (e z) r) v.grad ∧
        Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤
          Real.sqrt ((Real.sqrt Lam) ^ d) *
            Real.sqrt (integralAverage (euclideanBall (e z) r)
              (fun y => vecNormSq (v.grad y))) := by
  dsimp only
  let e := ellipticNormalizerContinuousLinearEquiv hA
  let T := ellipticNormalizer A
  let rho := R / Real.sqrt Lam
  let Y := euclideanBall (e z) rho
  have hYsub : Y ⊆ e '' euclideanBall z R := by
    simpa only [Y, rho, e] using euclideanBall_subset_ellipticNormalizer_image hA hR z
  let v := (u.compLinearEquiv e).restrict (isOpen_euclideanBall _ _) hYsub
  have hrecover (x : Vec d) : matVecMul T (v.grad (e x)) = u.grad x := by
    rw [H1Function.restrict_grad,
      H1Function.comp_ellipticNormalizer_grad hA]
    simp only [e, ContinuousLinearEquiv.symm_apply_apply]
    change e (e.symm (u.grad x)) = u.grad x
    exact e.apply_symm_apply (u.grad x)
  refine ⟨hrecover, ?_⟩
  intro r hr hrrho
  have hsmall : euclideanBall (e z) r ⊆ Y := by
    dsimp [Y]
    exact euclideanBall_mono hr.le hrrho
  have hg : MemVectorL2On (euclideanBall (e z) r) v.grad := fun i =>
    (v.gradMemL2 i).mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hpull := ellipticNormalizer_pullback_mean_bounds hA hr z hg
  let f : Vec d → Vec d := fun x => matVecMul T (v.grad (e x))
  have hfun : f = u.grad := by
    funext x
    exact hrecover x
  constructor
  · simpa only [e, T, f, hfun] using hpull.2.1
  · have henergyFun :
        (fun x => vecNormSq (matVecMul T (v.grad (e x)))) =
          fun x => vecNormSq (u.grad x) := by
        funext x
        rw [hrecover x]
    rw [← henergyFun]
    simpa only [e, T] using hpull.2.2

end

end PDE
