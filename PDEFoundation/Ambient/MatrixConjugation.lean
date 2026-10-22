module

public import PDEFoundation.Ambient.EllipticNormalization
public import PDEFoundation.Ambient.MatrixLinearEquiv
public import PDEFoundation.Ambient.MatrixPerturbation

/-!
# Quantitative conjugation by the elliptic normalizer
-/

@[expose] public section

namespace PDE

noncomputable section

private theorem matVecMul_mul {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul (A * B) x = matVecMul A (matVecMul B x) := by
  classical
  change (A * B).mulVec x = A.mulVec (B.mulVec x)
  exact (Matrix.mulVec_mulVec x A B).symm

private theorem matVecMul_sub {d : ℕ} (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  classical
  change (A - B).mulVec x = A.mulVec x - B.mulVec x
  exact Matrix.sub_mulVec A B x

private theorem matVecMul_one {d : ℕ} (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  classical
  exact Matrix.one_mulVec x

/-- The canonical normalizer is symmetric under unit lower ellipticity. -/
theorem ellipticNormalizer_transpose_of_isEllipticMatrix
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0) :
    matTranspose (ellipticNormalizer A0) = ellipticNormalizer A0 := by
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A0 x) := by
    intro x
    simpa only [one_mul] using hA0.coercive x
  exact ellipticNormalizer_transpose (symmPart_posDef_of_one_le hone)

/-- Removing the skew part before conjugation is exactly the same as
conjugating the raw coefficient difference and subtracting the identity. -/
theorem ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one
    {d : ℕ} {Lam : ℝ} {A0 B : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0) :
    ellipticNormalizer A0 * (B - skewPart A0) *
          matTranspose (ellipticNormalizer A0) - 1 =
      ellipticNormalizer A0 * (B - A0) *
        matTranspose (ellipticNormalizer A0) := by
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A0 x) := by
    intro x
    simpa only [one_mul] using hA0.coercive x
  have hS : (symmPart A0).PosDef := symmPart_posDef_of_one_le hone
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
    _ = ellipticNormalizer A0 * ((B - skewPart A0) - symmPart A0) *
          matTranspose (ellipticNormalizer A0) := by noncomm_ring
    _ = ellipticNormalizer A0 * (B - A0) *
          matTranspose (ellipticNormalizer A0) := by rw [hsub]

/-- A Euclidean operator perturbation remains of the same size after the
canonical elliptic normalization and removal of the skew part. -/
theorem isMatrixPerturbationLE_ellipticNormalizer_conjugation
    {d : ℕ} {Lam delta : ℝ} {A0 B : Mat d}
    (hA0 : IsEllipticMatrix 1 Lam A0) (hdelta : 0 ≤ delta)
    (hBA0 : IsMatrixPerturbationLE delta B A0) :
    IsMatrixPerturbationLE delta
      (ellipticNormalizer A0 * (B - skewPart A0) *
        matTranspose (ellipticNormalizer A0))
      (1 : Mat d) := by
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A0 x) := by
    intro x
    simpa only [one_mul] using hA0.coercive x
  have hTbound := vecEuclideanNorm_ellipticNormalizer_mulVec_le hone
  have hTsymm := ellipticNormalizer_transpose_of_isEllipticMatrix hA0
  intro x
  rw [ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one hA0,
    matVecMul_mul, matVecMul_mul, hTsymm]
  calc
    vecEuclideanNorm
        (matVecMul (ellipticNormalizer A0)
          (matVecMul (B - A0) (matVecMul (ellipticNormalizer A0) x))) ≤
        vecEuclideanNorm
          (matVecMul (B - A0) (matVecMul (ellipticNormalizer A0) x)) := hTbound _
    _ ≤ delta * vecEuclideanNorm (matVecMul (ellipticNormalizer A0) x) := hBA0 _
    _ ≤ delta * vecEuclideanNorm x :=
      mul_le_mul_of_nonneg_left (hTbound x) hdelta

/-- The canonical normalizer as an actual native continuous linear
equivalence. -/
noncomputable def ellipticNormalizerContinuousLinearEquiv
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0) :
    Vec d ≃L[ℝ] Vec d := by
  have hone : ∀ x : Vec d, vecNormSq x ≤ vecDot x (matVecMul A0 x) := by
    intro x
    simpa only [one_mul] using hA0.coercive x
  exact matrixContinuousLinearEquiv (ellipticNormalizer A0)
    (ellipticNormalizer_isUnit (symmPart_posDef_of_one_le hone))

@[simp]
theorem ellipticNormalizerContinuousLinearEquiv_apply
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0)
    (x : Vec d) :
    ellipticNormalizerContinuousLinearEquiv hA0 x =
      matVecMul (ellipticNormalizer A0) x :=
  rfl

@[simp]
theorem ellipticNormalizerContinuousLinearEquiv_symm_apply
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0)
    (x : Vec d) :
    (ellipticNormalizerContinuousLinearEquiv hA0).symm x =
      matVecMul (ellipticNormalizer A0)⁻¹ x :=
  rfl

theorem vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_le
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0)
    (x : Vec d) :
    vecEuclideanNorm (ellipticNormalizerContinuousLinearEquiv hA0 x) ≤
      vecEuclideanNorm x := by
  rw [ellipticNormalizerContinuousLinearEquiv_apply]
  have hone : ∀ y : Vec d, vecNormSq y ≤ vecDot y (matVecMul A0 y) := by
    intro y
    simpa only [one_mul] using hA0.coercive y
  exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hone x

theorem vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_symm_le
    {d : ℕ} {Lam : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0)
    (x : Vec d) :
    vecEuclideanNorm ((ellipticNormalizerContinuousLinearEquiv hA0).symm x) ≤
      Real.sqrt Lam * vecEuclideanNorm x := by
  rw [ellipticNormalizerContinuousLinearEquiv_symm_apply]
  exact vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le hA0 x

end

end PDE
