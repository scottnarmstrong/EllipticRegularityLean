module

public import PDEFoundation.Ambient.EllipticQuadraticNormalization
public import PDEFoundation.Ambient.MatrixLinearEquiv
public import PDEFoundation.Ambient.MatrixPerturbation

/-! # Matrix conjugation from quadratic ellipticity bounds -/

@[expose] public section

namespace PDE

noncomputable section

private theorem quadratic_matVecMul_mul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul (A * B) x = matVecMul A (matVecMul B x) := by
  classical
  change (A * B).mulVec x = A.mulVec (B.mulVec x)
  exact (Matrix.mulVec_mulVec x A B).symm

/-- The canonical normalizer is symmetric under a unit lower quadratic
coercivity bound. -/
theorem ellipticNormalizer_transpose_of_quadratic_lower
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi)) :
    matTranspose (ellipticNormalizer A0) = ellipticNormalizer A0 :=
  ellipticNormalizer_transpose (symmPart_posDef_of_one_le hLower)

/-- Removing the skew part before normalization gives exactly the
conjugated coefficient difference. -/
theorem ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one_of_quadratic_lower
    {d : ℕ} {A0 B : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi)) :
    ellipticNormalizer A0 * (B - skewPart A0) *
          matTranspose (ellipticNormalizer A0) - 1 =
      ellipticNormalizer A0 * (B - A0) *
        matTranspose (ellipticNormalizer A0) := by
  have hS : (symmPart A0).PosDef := symmPart_posDef_of_one_le hLower
  have hnormalize := ellipticNormalizer_mul_symmPart_mul_transpose hS
  have hdecomp : A0 = symmPart A0 + skewPart A0 := by
    ext i j
    simp [symmPart, skewPart]
    ring
  have hsub : (B - skewPart A0) - symmPart A0 = B - A0 := by
    calc
      (B - skewPart A0) - symmPart A0 =
          B - (symmPart A0 + skewPart A0) := by abel
      _ = B - A0 := by rw [← hdecomp]
  calc
    ellipticNormalizer A0 * (B - skewPart A0) *
          matTranspose (ellipticNormalizer A0) - 1 =
        ellipticNormalizer A0 * (B - skewPart A0) *
          matTranspose (ellipticNormalizer A0) -
            ellipticNormalizer A0 * symmPart A0 *
              matTranspose (ellipticNormalizer A0) := by rw [hnormalize]
    _ = ellipticNormalizer A0 *
          ((B - skewPart A0) - symmPart A0) *
            matTranspose (ellipticNormalizer A0) := by noncomm_ring
    _ = ellipticNormalizer A0 * (B - A0) *
          matTranspose (ellipticNormalizer A0) := by rw [hsub]

/-- A Euclidean operator perturbation retains the same size after quadratic
normalization and removal of the skew part. -/
theorem isMatrixPerturbationLE_ellipticNormalizer_conjugation_of_quadratic_lower
    {d : ℕ} {delta : ℝ} {A0 B : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hdelta : 0 ≤ delta) (hBA0 : IsMatrixPerturbationLE delta B A0) :
    IsMatrixPerturbationLE delta
      (ellipticNormalizer A0 * (B - skewPart A0) *
        matTranspose (ellipticNormalizer A0))
      (1 : Mat d) := by
  have hTbound := vecEuclideanNorm_ellipticNormalizer_mulVec_le hLower
  have hTsymm := ellipticNormalizer_transpose_of_quadratic_lower hLower
  intro x
  rw [ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one_of_quadratic_lower
      hLower,
    quadratic_matVecMul_mul, quadratic_matVecMul_mul, hTsymm]
  calc
    vecEuclideanNorm
        (matVecMul (ellipticNormalizer A0)
          (matVecMul (B - A0) (matVecMul (ellipticNormalizer A0) x))) ≤
        vecEuclideanNorm
          (matVecMul (B - A0) (matVecMul (ellipticNormalizer A0) x)) := hTbound _
    _ ≤ delta * vecEuclideanNorm (matVecMul (ellipticNormalizer A0) x) := hBA0 _
    _ ≤ delta * vecEuclideanNorm x :=
      mul_le_mul_of_nonneg_left (hTbound x) hdelta

/-- The quadratic normalizer as a native continuous linear equivalence. -/
noncomputable def quadraticEllipticNormalizerContinuousLinearEquiv
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi)) :
    Vec d ≃L[ℝ] Vec d :=
  matrixContinuousLinearEquiv (ellipticNormalizer A0)
    (ellipticNormalizer_isUnit (symmPart_posDef_of_one_le hLower))

@[simp]
theorem quadraticEllipticNormalizerContinuousLinearEquiv_apply
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (x : Vec d) :
    quadraticEllipticNormalizerContinuousLinearEquiv hLower x =
      matVecMul (ellipticNormalizer A0) x :=
  rfl

@[simp]
theorem quadraticEllipticNormalizerContinuousLinearEquiv_symm_apply
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (x : Vec d) :
    (quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm x =
      matVecMul (ellipticNormalizer A0)⁻¹ x :=
  rfl

/-- The forward quadratic normalizer is a Euclidean contraction. -/
theorem vecEuclideanNorm_quadraticEllipticNormalizerContinuousLinearEquiv_le
    {d : ℕ} {A0 : Mat d}
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (x : Vec d) :
    vecEuclideanNorm
        (quadraticEllipticNormalizerContinuousLinearEquiv hLower x) ≤
      vecEuclideanNorm x := by
  rw [quadraticEllipticNormalizerContinuousLinearEquiv_apply]
  exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hLower x

/-- The inverse quadratic normalizer is bounded by the square root of the
upper quadratic constant. -/
theorem vecEuclideanNorm_quadraticEllipticNormalizerContinuousLinearEquiv_symm_le
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hLam : 0 ≤ Lam)
    (hLower : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A0 xi))
    (hUpper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A0) xi) ≤ Lam * vecNormSq xi)
    (x : Vec d) :
    vecEuclideanNorm
        ((quadraticEllipticNormalizerContinuousLinearEquiv hLower).symm x) ≤
      Real.sqrt Lam * vecEuclideanNorm x := by
  rw [quadraticEllipticNormalizerContinuousLinearEquiv_symm_apply]
  exact
    vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
      hLam hLower hUpper x

end

end PDE
