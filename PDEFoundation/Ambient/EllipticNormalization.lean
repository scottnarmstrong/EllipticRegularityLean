module

public import PDEFoundation.Ambient.CoefficientField
public import Mathlib.Analysis.Matrix.Order

/-!
# Normalization of constant elliptic matrices

This module constructs the inverse positive square root of the symmetric part
of a constant elliptic matrix.  All statements use the native `Vec` and `Mat`
carriers and the explicit Euclidean norm.
-/

@[expose] public section

open scoped MatrixOrder

namespace PDE

noncomputable section

/-- The symmetric positive matrix associated with a coefficient matrix. -/
abbrev ellipticSymmPart {d : ℕ} (A : Mat d) : Mat d :=
  symmPart A

theorem vecDot_symmPart_matVecMul {d : ℕ} (A : Mat d) (xi : Vec d) :
    vecDot xi (matVecMul (symmPart A) xi) = vecDot xi (matVecMul A xi) := by
  classical
  have htranspose :
      vecDot xi (matVecMul (matTranspose A) xi) =
        vecDot xi (matVecMul A xi) := by
    calc
      vecDot xi (matVecMul (matTranspose A) xi)
          = ∑ i, ∑ j, xi i * (A j i * xi j) := by
            unfold vecDot matVecMul matTranspose
            congr with i
            rw [Finset.mul_sum]
            simp only [Matrix.transpose_apply]
      _ = ∑ j, ∑ i, (A j i * xi i) * xi j := by
            rw [Finset.sum_comm]
            congr with j
            congr with i
            ring
      _ = vecDot xi (matVecMul A xi) := by
            unfold vecDot matVecMul
            congr with j
            rw [Finset.mul_sum]
            congr with i
            ring
  have haction : matVecMul (symmPart A) xi =
      (1 / 2 : ℝ) • (matVecMul A xi + matVecMul (matTranspose A) xi) := by
    ext i
    unfold matVecMul symmPart matTranspose
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.transpose_apply,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hdot_add (y z : Vec d) :
      vecDot xi (y + z) = vecDot xi y + vecDot xi z := by
    simp only [vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hdot_smul (c : ℝ) (y : Vec d) :
      vecDot xi (c • y) = c * vecDot xi y := by
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      ∑ i, xi i * (c * y i) = ∑ i, c * (xi i * y i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = c * ∑ i, xi i * y i := by rw [Finset.mul_sum]
  rw [haction, hdot_smul, hdot_add, htranspose]
  ring

theorem symmPart_posDef_of_one_le {d : ℕ} {A : Mat d}
    (hcoercive : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A xi)) :
    (symmPart A).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact matTranspose_symmPart A
  · intro xi hxi
    have hnorm_pos : 0 < vecNormSq xi := by
      rw [vecNormSq_eq_sum_sq]
      obtain ⟨i, hi⟩ : ∃ i, xi i ≠ 0 := by
        simpa [funext_iff] using hxi
      exact Finset.sum_pos' (fun j _ => sq_nonneg (xi j))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have h := hcoercive xi
    rw [← vecDot_symmPart_matVecMul A xi] at h
    exact hnorm_pos.trans_le h

/-- The native normalization matrix: the inverse positive square root of the
symmetric part. -/
noncomputable def ellipticNormalizer {d : ℕ} (A : Mat d) : Mat d :=
  (CFC.sqrt (symmPart A))⁻¹

theorem ellipticNormalizer_isUnit {d : ℕ} {A : Mat d}
    (hS : (symmPart A).PosDef) : IsUnit (ellipticNormalizer A) := by
  classical
  unfold ellipticNormalizer
  exact Matrix.isUnit_nonsing_inv_iff.mpr <|
    (CFC.isUnit_sqrt_iff (symmPart A) hS.posSemidef.nonneg).mpr hS.isUnit

theorem ellipticNormalizer_transpose {d : ℕ} {A : Mat d}
    (hS : (symmPart A).PosDef) :
    matTranspose (ellipticNormalizer A) = ellipticNormalizer A := by
  classical
  have hsqrt : (CFC.sqrt (symmPart A)).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hS.isStrictlyPositive.sqrt
  exact hsqrt.inv.isHermitian

theorem ellipticNormalizer_mul_symmPart_mul_transpose {d : ℕ} {A : Mat d}
    (hS : (symmPart A).PosDef) :
    ellipticNormalizer A * symmPart A * matTranspose (ellipticNormalizer A) = 1 := by
  classical
  let R : Mat d := CFC.sqrt (symmPart A)
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff (symmPart A) hS.posSemidef.nonneg).mpr hS.isUnit
  have hRsq : R * R = symmPart A := CFC.sqrt_mul_sqrt_self (symmPart A)
  have hRinv_symm : matTranspose R⁻¹ = R⁻¹ :=
    (Matrix.isStrictlyPositive_iff_posDef.mp hS.isStrictlyPositive.sqrt).inv.isHermitian
  change R⁻¹ * symmPart A * matTranspose R⁻¹ = 1
  rw [hRinv_symm, ← hRsq]
  let := hRunit.invertible
  simp

theorem nonsingInv_ellipticNormalizer_mul_transpose {d : ℕ} {A : Mat d}
    (hS : (symmPart A).PosDef) :
    (ellipticNormalizer A)⁻¹ * matTranspose (ellipticNormalizer A)⁻¹ =
      symmPart A := by
  classical
  let R : Mat d := CFC.sqrt (symmPart A)
  have hRunit : IsUnit R :=
    (CFC.isUnit_sqrt_iff (symmPart A) hS.posSemidef.nonneg).mpr hS.isUnit
  have hTinv : (ellipticNormalizer A)⁻¹ = R := by
    change (R⁻¹)⁻¹ = R
    exact Matrix.nonsing_inv_nonsing_inv R (R.isUnit_iff_isUnit_det.mp hRunit)
  rw [hTinv]
  have hRsymm : matTranspose R = R :=
    (Matrix.isStrictlyPositive_iff_posDef.mp hS.isStrictlyPositive.sqrt).isHermitian
  rw [hRsymm]
  exact CFC.sqrt_mul_sqrt_self (symmPart A)

private theorem vecDot_matVecMul_congruence {d : ℕ}
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

private theorem vecDot_matVecMul_one {d : ℕ} (xi : Vec d) :
    vecDot xi (matVecMul (1 : Mat d) xi) = vecNormSq xi := by
  classical
  change xi ⬝ᵥ (1 : Mat d).mulVec xi = vecNormSq xi
  rw [Matrix.one_mulVec]
  rfl

theorem symmPart_quadratic_upper_of_isEllipticMatrix
    {d : ℕ} {Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Lam A) (xi : Vec d) :
    vecDot xi (matVecMul (symmPart A) xi) ≤ Lam * vecNormSq xi := by
  rw [vecDot_symmPart_matVecMul]
  calc
    vecDot xi (matVecMul A xi) ≤ |vecDot xi (matVecMul A xi)| := le_abs_self _
    _ ≤ vecEuclideanNorm xi * vecEuclideanNorm (matVecMul A xi) :=
      abs_vecDot_le_vecEuclideanNorm_mul xi _
    _ ≤ vecEuclideanNorm xi * (Lam * vecEuclideanNorm xi) :=
      mul_le_mul_of_nonneg_left
        (vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix hA xi)
        (vecEuclideanNorm_nonneg xi)
    _ = Lam * vecNormSq xi := by
      calc
        vecEuclideanNorm xi * (Lam * vecEuclideanNorm xi) =
            Lam * (vecEuclideanNorm xi * vecEuclideanNorm xi) := by ring
        _ = Lam * vecNormSq xi := by rw [← pow_two, vecEuclideanNorm_sq]

theorem vecNormSq_ellipticNormalizer_mulVec_le {d : ℕ} {A : Mat d}
    (hcoercive : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A xi))
    (xi : Vec d) :
    vecNormSq (matVecMul (ellipticNormalizer A) xi) ≤ vecNormSq xi := by
  classical
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hcoercive
  calc
    vecNormSq (matVecMul (ellipticNormalizer A) xi) ≤
        vecDot (matVecMul (ellipticNormalizer A) xi)
          (matVecMul A (matVecMul (ellipticNormalizer A) xi)) := hcoercive _
    _ = vecDot (matVecMul (ellipticNormalizer A) xi)
        (matVecMul (symmPart A) (matVecMul (ellipticNormalizer A) xi)) := by
      rw [vecDot_symmPart_matVecMul]
    _ = vecDot xi (matVecMul
        (matTranspose (ellipticNormalizer A) * symmPart A * ellipticNormalizer A) xi) :=
      vecDot_matVecMul_congruence _ _ _
    _ = vecNormSq xi := by
      have hTsymm := ellipticNormalizer_transpose hS
      have hnormalize := ellipticNormalizer_mul_symmPart_mul_transpose hS
      rw [hTsymm] at hnormalize
      rw [hTsymm, hnormalize, vecDot_matVecMul_one]

theorem vecEuclideanNorm_ellipticNormalizer_mulVec_le {d : ℕ} {A : Mat d}
    (hcoercive : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A xi))
    (xi : Vec d) :
    vecEuclideanNorm (matVecMul (ellipticNormalizer A) xi) ≤ vecEuclideanNorm xi := by
  unfold vecEuclideanNorm
  exact Real.sqrt_le_sqrt (vecNormSq_ellipticNormalizer_mulVec_le hcoercive xi)

theorem vecNormSq_nonsingInv_ellipticNormalizer_mulVec_le
    {d : ℕ} {Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Lam A) (xi : Vec d) :
    vecNormSq (matVecMul (ellipticNormalizer A)⁻¹ xi) ≤ Lam * vecNormSq xi := by
  classical
  have hone : ∀ eta : Vec d, vecNormSq eta ≤ vecDot eta (matVecMul A eta) := by
    intro eta
    simpa only [one_mul] using hA.coercive eta
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hone
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
          (matVecMul (1 : Mat d) (matVecMul (ellipticNormalizer A)⁻¹ xi)) := by
      rw [vecDot_matVecMul_one]
    _ = vecDot xi (matVecMul
        (matTranspose (ellipticNormalizer A)⁻¹ * (1 : Mat d) *
          (ellipticNormalizer A)⁻¹) xi) :=
      vecDot_matVecMul_congruence _ _ _
    _ = vecDot xi (matVecMul (symmPart A) xi) := by rw [hBsymm, Matrix.mul_one, hBsquare]
    _ ≤ Lam * vecNormSq xi := symmPart_quadratic_upper_of_isEllipticMatrix hA xi

theorem vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le
    {d : ℕ} {Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Lam A) (xi : Vec d) :
    vecEuclideanNorm (matVecMul (ellipticNormalizer A)⁻¹ xi) ≤
      Real.sqrt Lam * vecEuclideanNorm xi := by
  have hsquare := vecNormSq_nonsingInv_ellipticNormalizer_mulVec_le hA xi
  have hLam : 0 ≤ Lam := hA.Lam_pos.le
  unfold vecEuclideanNorm
  calc
    √(vecNormSq (matVecMul (ellipticNormalizer A)⁻¹ xi)) ≤
        √(Lam * vecNormSq xi) := Real.sqrt_le_sqrt hsquare
    _ = √Lam * √(vecNormSq xi) := Real.sqrt_mul hLam _

/-- Quantitative native-matrix normalization of a constant uniformly elliptic
coefficient matrix whose lower ellipticity constant is one. -/
theorem exists_ellipticNormalizer {d : ℕ} {Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Lam A) :
    ∃ T : Mat d,
      IsUnit T ∧
      T * symmPart A * matTranspose T = 1 ∧
      (∀ xi : Vec d,
        vecEuclideanNorm (matVecMul T xi) ≤ vecEuclideanNorm xi) ∧
      ∀ xi : Vec d,
        vecEuclideanNorm (matVecMul T⁻¹ xi) ≤
          Real.sqrt Lam * vecEuclideanNorm xi := by
  have hone : ∀ xi : Vec d, vecNormSq xi ≤ vecDot xi (matVecMul A xi) := by
    intro xi
    simpa only [one_mul] using hA.coercive xi
  have hS : (symmPart A).PosDef := symmPart_posDef_of_one_le hone
  refine ⟨ellipticNormalizer A, ellipticNormalizer_isUnit hS,
    ellipticNormalizer_mul_symmPart_mul_transpose hS, ?_, ?_⟩
  · exact vecEuclideanNorm_ellipticNormalizer_mulVec_le hone
  · exact vecEuclideanNorm_nonsingInv_ellipticNormalizer_mulVec_le hA

end

end PDE
