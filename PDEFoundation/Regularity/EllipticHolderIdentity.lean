module

public import PDEFoundation.Regularity.EllipticHolderTransport

/-! # Hölder data at normalized elliptic coordinates -/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The normalized forcing has the transported Euclidean Hölder bound on the
full image domain. -/
theorem normalizedForcing_holder
    {U : Set (Vec d)} {F : Vec d → Vec d} {A0 : Mat d}
    {Lam alpha KF : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (halpha : 0 < alpha) (hKF : 0 ≤ KF)
    (hF : EuclideanFieldHolderSeminormLE U F alpha KF) :
    EuclideanFieldHolderSeminormLE
      (ellipticNormalizerContinuousLinearEquiv hA0 '' U)
      (fun y => matVecMul (ellipticNormalizer A0)
        (F ((ellipticNormalizerContinuousLinearEquiv hA0).symm y)))
      alpha (Real.sqrt Lam ^ alpha * KF) :=
  euclideanFieldHolderSeminormLE_ellipticNormalizer hA0 halpha hKF hF

/-- The normalized coefficient has the transported operator Hölder bound on
the full image domain. -/
theorem normalizedCoefficient_holder
    {U : Set (Vec d)} {a : CoeffField d} {A0 : Mat d}
    {Lam alpha Ka : ℝ} (hA0 : IsEllipticMatrix 1 Lam A0)
    (halpha : 0 < alpha) (hKa : 0 ≤ Ka)
    (ha : EuclideanMatrixHolderSeminormLE U a alpha Ka) :
    EuclideanMatrixHolderSeminormLE
      (ellipticNormalizerContinuousLinearEquiv hA0 '' U)
      (fun y => ellipticNormalizer A0 *
        (a ((ellipticNormalizerContinuousLinearEquiv hA0).symm y) - skewPart A0) *
          matTranspose (ellipticNormalizer A0))
      alpha (Real.sqrt Lam ^ alpha * Ka) :=
  euclideanMatrixHolderSeminormLE_ellipticNormalizer hA0 halpha hKa ha

/-- If the given matrix is the coefficient at `z`, the normalized
coefficient is exactly the identity at the image of `z`. -/
theorem normalizedCoefficient_apply_image_eq_one
    {a : CoeffField d} {A0 : Mat d} {Lam : ℝ}
    (hA0 : IsEllipticMatrix 1 Lam A0) {z : Vec d} (hz : a z = A0) :
    ellipticNormalizer A0 *
        (a ((ellipticNormalizerContinuousLinearEquiv hA0).symm
          (ellipticNormalizerContinuousLinearEquiv hA0 z)) - skewPart A0) *
      matTranspose (ellipticNormalizer A0) = 1 := by
  rw [ContinuousLinearEquiv.symm_apply_apply, hz]
  have h := ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one
    (B := A0) hA0
  simp only [sub_self, Matrix.mul_zero, zero_mul] at h
  exact sub_eq_zero.mp h

end

end PDE
