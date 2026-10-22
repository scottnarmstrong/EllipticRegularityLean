module

public import PDEFoundation.Ambient.MatrixConjugation
public import PDEFoundation.Regularity.FieldHolder

/-!
# Hölder bounds under elliptic normalization

This file transports Euclidean Hölder bounds through the canonical linear
change of variables attached to a constant elliptic matrix.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

private theorem matVecMul_sub (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  change A.mulVec (x - y) = A.mulVec x - A.mulVec y
  exact Matrix.mulVec_sub A x y

private theorem matVecMul_mul (A B : Mat d) (x : Vec d) :
    matVecMul (A * B) x = matVecMul A (matVecMul B x) := by
  change (A * B).mulVec x = A.mulVec (B.mulVec x)
  exact (Matrix.mulVec_mulVec x A B).symm

private theorem normalizer_symm_distance_rpow_le
    {Lam alpha : ℝ} {A0 : Mat d} (hA0 : IsEllipticMatrix 1 Lam A0)
    (halpha : 0 < alpha) (x y : Vec d) :
    vecEuclideanNorm
          ((ellipticNormalizerContinuousLinearEquiv hA0).symm x -
            (ellipticNormalizerContinuousLinearEquiv hA0).symm y) ^ alpha ≤
      Real.sqrt Lam ^ alpha * vecEuclideanNorm (x - y) ^ alpha := by
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  have hdist :
      vecEuclideanNorm (e.symm x - e.symm y) ≤
        Real.sqrt Lam * vecEuclideanNorm (x - y) := by
    rw [← e.symm.map_sub]
    exact vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_symm_le
      hA0 (x - y)
  calc
    vecEuclideanNorm (e.symm x - e.symm y) ^ alpha ≤
        (Real.sqrt Lam * vecEuclideanNorm (x - y)) ^ alpha :=
      Real.rpow_le_rpow (vecEuclideanNorm_nonneg _) hdist halpha.le
    _ = Real.sqrt Lam ^ alpha * vecEuclideanNorm (x - y) ^ alpha := by
      rw [Real.mul_rpow (Real.sqrt_nonneg Lam) (vecEuclideanNorm_nonneg _)]

/-- A vector-field Hölder bound transported through the canonical elliptic
normalizing coordinates. -/
theorem euclideanFieldHolderSeminormLE_ellipticNormalizer
    {U : Set (Vec d)} {F : Vec d → Vec d} {A0 : Mat d} {Lam alpha KF : ℝ}
    (hA0 : IsEllipticMatrix 1 Lam A0) (halpha : 0 < alpha) (hKF : 0 ≤ KF)
    (hF : EuclideanFieldHolderSeminormLE U F alpha KF) :
    EuclideanFieldHolderSeminormLE
      (ellipticNormalizerContinuousLinearEquiv hA0 '' U)
      (fun y => matVecMul (ellipticNormalizer A0)
        (F ((ellipticNormalizerContinuousLinearEquiv hA0).symm y)))
      alpha (Real.sqrt Lam ^ alpha * KF) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  intro x hx y hy
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [← matVecMul_sub]
  have hT := vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_le
    hA0 (F x0 - F y0)
  rw [ellipticNormalizerContinuousLinearEquiv_apply] at hT
  calc
    vecEuclideanNorm (matVecMul (ellipticNormalizer A0) (F x0 - F y0)) ≤
        vecEuclideanNorm (F x0 - F y0) := hT
    _ ≤ KF * vecEuclideanNorm (x0 - y0) ^ alpha := hF x0 hx0 y0 hy0
    _ ≤ KF * (Real.sqrt Lam ^ alpha *
          vecEuclideanNorm (e x0 - e y0) ^ alpha) :=
      mul_le_mul_of_nonneg_left
        (by
          have hr := normalizer_symm_distance_rpow_le hA0 halpha (e x0) (e y0)
          change vecEuclideanNorm (e.symm (e x0) - e.symm (e y0)) ^ alpha ≤ _ at hr
          simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr) hKF
    _ = (Real.sqrt Lam ^ alpha * KF) *
          vecEuclideanNorm (e x0 - e y0) ^ alpha := by ring

/-- A matrix-field Hölder bound transported by canonical elliptic
conjugation after removal of the skew part. -/
theorem euclideanMatrixHolderSeminormLE_ellipticNormalizer
    {U : Set (Vec d)} {a : CoeffField d} {A0 : Mat d} {Lam alpha Ka : ℝ}
    (hA0 : IsEllipticMatrix 1 Lam A0) (halpha : 0 < alpha) (hKa : 0 ≤ Ka)
    (ha : EuclideanMatrixHolderSeminormLE U a alpha Ka) :
    EuclideanMatrixHolderSeminormLE
      (ellipticNormalizerContinuousLinearEquiv hA0 '' U)
      (fun y => ellipticNormalizer A0 *
        (a ((ellipticNormalizerContinuousLinearEquiv hA0).symm y) - skewPart A0) *
          matTranspose (ellipticNormalizer A0))
      alpha (Real.sqrt Lam ^ alpha * Ka) := by
  let e := ellipticNormalizerContinuousLinearEquiv hA0
  let T := ellipticNormalizer A0
  intro x hx y hy xi
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hdiff :
      T * (a x0 - skewPart A0) * matTranspose T -
          T * (a y0 - skewPart A0) * matTranspose T =
        T * (a x0 - a y0) * T := by
    rw [ellipticNormalizer_transpose_of_isEllipticMatrix hA0]
    noncomm_ring
  rw [hdiff, matVecMul_mul, matVecMul_mul]
  have hTleft := vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_le hA0
    (matVecMul (a x0 - a y0) (matVecMul T xi))
  have hTright := vecEuclideanNorm_ellipticNormalizerContinuousLinearEquiv_le hA0 xi
  rw [ellipticNormalizerContinuousLinearEquiv_apply] at hTleft hTright
  calc
    vecEuclideanNorm
        (matVecMul T (matVecMul (a x0 - a y0) (matVecMul T xi))) ≤
      vecEuclideanNorm (matVecMul (a x0 - a y0) (matVecMul T xi)) := hTleft
    _ ≤ (Ka * vecEuclideanNorm (x0 - y0) ^ alpha) *
        vecEuclideanNorm (matVecMul T xi) := ha x0 hx0 y0 hy0 _
    _ ≤ (Ka * vecEuclideanNorm (x0 - y0) ^ alpha) *
        vecEuclideanNorm xi :=
      mul_le_mul_of_nonneg_left hTright
        (mul_nonneg hKa (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) alpha))
    _ ≤ ((Ka * (Real.sqrt Lam ^ alpha *
          vecEuclideanNorm (e x0 - e y0) ^ alpha)) * vecEuclideanNorm xi) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (by
            have hr := normalizer_symm_distance_rpow_le hA0 halpha (e x0) (e y0)
            change vecEuclideanNorm (e.symm (e x0) - e.symm (e y0)) ^ alpha ≤ _ at hr
            simpa only [ContinuousLinearEquiv.symm_apply_apply] using hr) hKa)
        (vecEuclideanNorm_nonneg xi)
    _ = ((Real.sqrt Lam ^ alpha * Ka) *
          vecEuclideanNorm (e x0 - e y0) ^ alpha) * vecEuclideanNorm xi := by ring

end

end PDE
