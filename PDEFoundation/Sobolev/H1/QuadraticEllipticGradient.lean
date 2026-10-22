module

public import PDEFoundation.Ambient.QuadraticMatrixConjugation
public import PDEFoundation.Sobolev.H1.Linear

/-! # Gradient transport under quadratic elliptic normalization -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem vecDot_quadratic_nonsingInv_mulVec_basisVec
    (T : Mat d) (hT : matTranspose T = T) (g : Vec d) (i : Fin d) :
    vecDot g (matVecMul T⁻¹ (basisVec i)) = matVecMul T⁻¹ g i := by
  have hInv : matTranspose T⁻¹ = T⁻¹ := by
    calc
      matTranspose T⁻¹ = (matTranspose T)⁻¹ := by
        simpa only [matTranspose] using (Matrix.transpose_nonsing_inv (A := T))
      _ = T⁻¹ := by rw [hT]
  have hb (j : Fin d) : matVecMul T⁻¹ (basisVec i) j = T⁻¹ j i := by
    change T⁻¹.mulVec (Pi.single i 1) j = T⁻¹ j i
    simp [Matrix.mulVec_single, Matrix.col]
  unfold vecDot
  simp_rw [hb]
  calc
    ∑ j, g j * T⁻¹ j i = ∑ j, T⁻¹ j i * g j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = matVecMul T⁻¹ g i := by
      unfold matVecMul
      apply Finset.sum_congr rfl
      intro j _
      have hij := congrArg (fun A : Mat d => A i j) hInv
      simpa only [matTranspose, Matrix.transpose_apply] using
        congrArg (fun c => c * g j) hij

namespace H1Function

/-- The actual weak gradient under quadratic normalization is multiplication
by the inverse normalizer. -/
theorem comp_quadraticEllipticNormalizer_grad
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (u : H1Function U) (y : Vec d) :
    (u.compLinearEquiv
      (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad y =
      matVecMul (ellipticNormalizer A0)⁻¹
        (u.grad
          ((quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm y)) := by
  funext i
  rw [compLinearEquiv_grad_apply,
    quadraticEllipticNormalizerContinuousLinearEquiv_symm_apply]
  exact vecDot_quadratic_nonsingInv_mulVec_basisVec _
    (ellipticNormalizer_transpose_of_quadratic_lower hLower) _ i

/-- Multiplying the normalized gradient by the normalizer recovers the
original gradient pointwise. -/
theorem quadraticEllipticNormalizer_mul_comp_grad
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (u : H1Function U) (x : Vec d) :
    matVecMul (ellipticNormalizer A0)
        ((u.compLinearEquiv
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad
            (quadraticEllipticNormalizerContinuousLinearEquiv hLower x)) =
      u.grad x := by
  rw [comp_quadraticEllipticNormalizer_grad hLower]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  change quadraticEllipticNormalizerContinuousLinearEquiv hLower
      ((quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm
        (u.grad x)) = u.grad x
  exact (quadraticEllipticNormalizerContinuousLinearEquiv hLower).apply_symm_apply _

/-- The normalized gradient has at most `sqrt Lam` Euclidean growth under the
upper quadratic bound. -/
theorem vecEuclideanNorm_comp_quadraticEllipticNormalizer_grad_le
    {A0 : Mat d} {Lam : ℝ} (hLam : 1 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    (u : H1Function U) (y : Vec d) :
    vecEuclideanNorm
        ((u.compLinearEquiv
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad y) ≤
      Real.sqrt Lam *
        vecEuclideanNorm
          (u.grad
            ((quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm y)) := by
  rw [comp_quadraticEllipticNormalizer_grad hLower]
  exact
    vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
      (zero_le_one.trans hLam) hLower hUpper _

/-- The original gradient is pointwise no larger than the normalized gradient
pulled to the corresponding point. -/
theorem vecEuclideanNorm_grad_le_comp_quadraticEllipticNormalizer_grad
    {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (u : H1Function U) (x : Vec d) :
    vecEuclideanNorm (u.grad x) ≤
      vecEuclideanNorm
        ((u.compLinearEquiv
          (quadraticEllipticNormalizerContinuousLinearEquiv hLower)).grad
            (quadraticEllipticNormalizerContinuousLinearEquiv hLower x)) := by
  rw [← quadraticEllipticNormalizer_mul_comp_grad hLower u x]
  exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hLower _

end H1Function

end

end PDE
