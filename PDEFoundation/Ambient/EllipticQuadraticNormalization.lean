module

public import PDEFoundation.Ambient.EllipticNormalization

/-! # Elliptic normalization from quadratic bounds -/

@[expose] public section

namespace PDE

noncomputable section

private theorem vecDot_matVecMul_congruence' {d : ℕ}
    (A B : Mat d) (xi : Vec d) :
    vecDot (matVecMul B xi) (matVecMul A (matVecMul B xi)) =
      vecDot xi (matVecMul (matTranspose B * A * B) xi) := by
  classical
  change B.mulVec xi ⬝ᵥ A.mulVec (B.mulVec xi) =
    xi ⬝ᵥ (B.transpose * A * B).mulVec xi
  calc
    B.mulVec xi ⬝ᵥ A.mulVec (B.mulVec xi) =
        A.mulVec (B.mulVec xi) ⬝ᵥ B.mulVec xi := dotProduct_comm _ _
    _ = Matrix.vecMul (A.mulVec (B.mulVec xi)) B ⬝ᵥ xi :=
      Matrix.dotProduct_mulVec _ _ _
    _ = xi ⬝ᵥ Matrix.vecMul (A.mulVec (B.mulVec xi)) B :=
      dotProduct_comm _ _
    _ = xi ⬝ᵥ B.transpose.mulVec (A.mulVec (B.mulVec xi)) := by
      rw [← Matrix.vecMul_transpose B.transpose]
      simp
    _ = xi ⬝ᵥ (B.transpose * A * B).mulVec xi := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem vecDot_matVecMul_one' {d : ℕ} (xi : Vec d) :
    vecDot xi (matVecMul (1 : Mat d) xi) = vecNormSq xi := by
  classical
  change xi ⬝ᵥ (1 : Mat d).mulVec xi = vecNormSq xi
  rw [Matrix.one_mulVec]
  rfl

/-- The inverse normalizer obeys the upper quadratic bound using only the
corresponding bound for the symmetric part. -/
theorem vecNormSq_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
    {d : ℕ} {Lam : ℝ} {A : Mat d}
    (hcoercive : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A xi))
    (hupper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A) xi) ≤ Lam * vecNormSq xi)
    (xi : Vec d) :
    vecNormSq (matVecMul (ellipticNormalizer A)⁻¹ xi) ≤
      Lam * vecNormSq xi := by
  classical
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hcoercive
  have hBsymm : matTranspose ((ellipticNormalizer A)⁻¹) =
      (ellipticNormalizer A)⁻¹ := by
    have hTsymm := ellipticNormalizer_transpose hS
    unfold matTranspose
    unfold matTranspose at hTsymm
    rw [Matrix.transpose_nonsing_inv, hTsymm]
  have hBsquare : (ellipticNormalizer A)⁻¹ * (ellipticNormalizer A)⁻¹ =
      symmPart A := by
    calc
      (ellipticNormalizer A)⁻¹ * (ellipticNormalizer A)⁻¹ =
          (ellipticNormalizer A)⁻¹ *
            matTranspose ((ellipticNormalizer A)⁻¹) := by rw [hBsymm]
      _ = symmPart A := nonsingInv_ellipticNormalizer_mul_transpose hS
  calc
    vecNormSq (matVecMul (ellipticNormalizer A)⁻¹ xi) =
        vecDot (matVecMul (ellipticNormalizer A)⁻¹ xi)
          (matVecMul (1 : Mat d)
            (matVecMul (ellipticNormalizer A)⁻¹ xi)) := by
      rw [vecDot_matVecMul_one']
    _ = vecDot xi (matVecMul
        (matTranspose (ellipticNormalizer A)⁻¹ * (1 : Mat d) *
          (ellipticNormalizer A)⁻¹) xi) :=
      vecDot_matVecMul_congruence' _ _ _
    _ = vecDot xi (matVecMul (symmPart A) xi) := by
      rw [hBsymm, Matrix.mul_one, hBsquare]
    _ ≤ Lam * vecNormSq xi := hupper xi

/-- Euclidean-norm form of the inverse-normalizer quadratic estimate. -/
theorem vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
    {d : ℕ} {Lam : ℝ} {A : Mat d} (hLam : 0 ≤ Lam)
    (hcoercive : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A xi))
    (hupper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A) xi) ≤ Lam * vecNormSq xi)
    (xi : Vec d) :
    vecEuclideanNorm (matVecMul (ellipticNormalizer A)⁻¹ xi) ≤
      Real.sqrt Lam * vecEuclideanNorm xi := by
  have hsquare :=
    vecNormSq_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
      hcoercive hupper xi
  unfold vecEuclideanNorm
  calc
    √(vecNormSq (matVecMul (ellipticNormalizer A)⁻¹ xi)) ≤
        √(Lam * vecNormSq xi) := Real.sqrt_le_sqrt hsquare
    _ = √Lam * √(vecNormSq xi) := Real.sqrt_mul hLam _

/-- The full normalization contract obtained from lower coercivity and an
upper quadratic bound for the symmetric part. -/
theorem exists_ellipticNormalizer_of_quadratic_bounds
    {d : ℕ} {Lam : ℝ} {A : Mat d} (hLam : 0 ≤ Lam)
    (hcoercive : ∀ xi : Vec d,
      vecNormSq xi ≤ vecDot xi (matVecMul A xi))
    (hupper : ∀ xi : Vec d,
      vecDot xi (matVecMul (symmPart A) xi) ≤ Lam * vecNormSq xi) :
    ∃ T : Mat d,
      IsUnit T ∧
      matTranspose T = T ∧
      T * symmPart A * matTranspose T = 1 ∧
      (∀ xi : Vec d,
        vecEuclideanNorm (matVecMul T xi) ≤ vecEuclideanNorm xi) ∧
      ∀ xi : Vec d,
        vecEuclideanNorm (matVecMul T⁻¹ xi) ≤
          Real.sqrt Lam * vecEuclideanNorm xi := by
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hcoercive
  refine ⟨ellipticNormalizer A, ellipticNormalizer_isUnit hS,
    ellipticNormalizer_transpose hS,
    ellipticNormalizer_mul_symmPart_mul_transpose hS, ?_, ?_⟩
  · exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hcoercive
  · exact
      vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le_of_quadratic_upper
        hLam hcoercive hupper

end

end PDE
