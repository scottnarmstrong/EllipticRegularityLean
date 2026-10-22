module

public import PDEFoundation.Ambient.MatrixPerturbation
public import PDEFoundation.Ambient.CoefficientField

@[expose] public section

namespace PDE

open Matrix

private theorem vecDot_smul_right_perturbation {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  unfold vecDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem isUnit_det_of_identity_perturbation
    {d : ℕ} {delta : ℝ} {A : Mat d}
    (hdelta : delta < 1)
    (hA : IsMatrixPerturbationLE delta A (1 : Mat d)) :
    IsUnit A.det := by
  apply A.isUnit_iff_isUnit_det.mp
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hzero : matVecMul A (x - y) = 0 := by
    change A.mulVec (x - y) = 0
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hcoerc :=
    one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
      hA (x - y)
  rw [hzero] at hcoerc
  have hsq : vecNormSq (x - y) = 0 := by
    have hnonneg := vecNormSq_nonneg (x - y)
    simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hcoerc
    nlinarith
  exact sub_eq_zero.mp (vecNormSq_eq_zero hsq)

/-- An identity perturbation of size at most one half becomes uniformly elliptic
with constants `1` and `9` after normalization by `1 - delta`. -/
theorem isEllipticMatrix_inv_one_sub_smul_of_isMatrixPerturbationLE
    {d : ℕ} {delta : ℝ} {A : Mat d}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 2)
    (hA : IsMatrixPerturbationLE delta A (1 : Mat d)) :
    IsEllipticMatrix 1 9 ((1 - delta)⁻¹ • A) := by
  have hone : 0 < 1 - delta := by linarith
  have honePlus : 0 ≤ 1 + delta := add_nonneg zero_le_one hdelta0
  have hdetA : IsUnit A.det :=
    isUnit_det_of_identity_perturbation (by linarith) hA
  have hc : (1 - delta)⁻¹ ≠ 0 := inv_ne_zero hone.ne'
  have hdetS : IsUnit (((1 - delta)⁻¹ • A).det) :=
    isUnit_det_smul hdetA hc
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro ξ
    have hbase :=
      one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
        hA ξ
    have hscaled := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hone.le)
    rw [show matVecMul ((1 - delta)⁻¹ • A) ξ =
        (1 - delta)⁻¹ • matVecMul A ξ by
      change (((1 - delta)⁻¹ • A).mulVec ξ) = _
      exact Matrix.smul_mulVec _ A ξ]
    have hdot := vecDot_smul_right_perturbation ξ (matVecMul A ξ) (1 - delta)⁻¹
    rw [hdot]
    have hcancel : (1 - delta)⁻¹ * (1 - delta) = 1 := inv_mul_cancel₀ hone.ne'
    calc
      1 * vecNormSq ξ = (1 - delta)⁻¹ * ((1 - delta) * vecNormSq ξ) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (1 - delta)⁻¹ * vecDot ξ (matVecMul A ξ) := hscaled
  · intro ξ
    let S : Mat d := (1 - delta)⁻¹ • A
    let η : Vec d := matVecMul S⁻¹ ξ
    have hSη : matVecMul S η = ξ := by
      change S.mulVec (S⁻¹.mulVec ξ) = ξ
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hdetS,
        Matrix.one_mulVec]
    have hactionA :=
      vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE
        hA η
    have haction : vecEuclideanNorm ξ ≤ 3 * vecEuclideanNorm η := by
      rw [← hSη]
      change vecEuclideanNorm (matVecMul ((1 - delta)⁻¹ • A) η) ≤ _
      rw [show matVecMul ((1 - delta)⁻¹ • A) η =
          (1 - delta)⁻¹ • matVecMul A η by
        change (((1 - delta)⁻¹ • A).mulVec η) = _
        exact Matrix.smul_mulVec _ A η,
        vecEuclideanNorm_smul]
      rw [abs_of_pos (inv_pos.mpr hone)]
      have hratio : (1 - delta)⁻¹ * (1 + delta) ≤ 3 := by
        apply (inv_mul_le_iff₀ hone).2
        nlinarith [honePlus]
      calc
        (1 - delta)⁻¹ * vecEuclideanNorm (matVecMul A η) ≤
            (1 - delta)⁻¹ * ((1 + delta) * vecEuclideanNorm η) :=
          mul_le_mul_of_nonneg_left hactionA (inv_nonneg.mpr hone.le)
        _ ≤ 3 * vecEuclideanNorm η := by
          nlinarith [vecEuclideanNorm_nonneg η]
    have hsqaction : vecNormSq ξ ≤ 9 * vecNormSq η := by
      have hs := mul_self_le_mul_self (vecEuclideanNorm_nonneg ξ) haction
      nlinarith [vecEuclideanNorm_sq ξ, vecEuclideanNorm_sq η]
    have hcoercη : vecNormSq η ≤ vecDot η (matVecMul S η) := by
      simpa only [S, one_mul] using
        (show 1 * vecNormSq η ≤
            vecDot η (matVecMul ((1 - delta)⁻¹ • A) η) from
          (by
            have hbase :=
              one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
                hA η
            have hscaled := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hone.le)
            rw [show matVecMul ((1 - delta)⁻¹ • A) η =
                (1 - delta)⁻¹ • matVecMul A η by
              change (((1 - delta)⁻¹ • A).mulVec η) = _
              exact Matrix.smul_mulVec _ A η]
            have hdot :=
              vecDot_smul_right_perturbation η (matVecMul A η) (1 - delta)⁻¹
            rw [hdot]
            have hcancel : (1 - delta)⁻¹ * (1 - delta) = 1 := inv_mul_cancel₀ hone.ne'
            calc
              1 * vecNormSq η =
                  (1 - delta)⁻¹ * ((1 - delta) * vecNormSq η) := by
                rw [← mul_assoc, hcancel, one_mul]
              _ ≤ (1 - delta)⁻¹ * vecDot η (matVecMul A η) := hscaled))
    change (9 : ℝ)⁻¹ * vecNormSq ξ ≤
      vecDot ξ (matVecMul S⁻¹ ξ)
    change (9 : ℝ)⁻¹ * vecNormSq ξ ≤ vecDot ξ η
    rw [← hSη, vecDot_comm]
    norm_num
    rw [← hSη] at hsqaction
    calc
      (1 / 9 : ℝ) * vecNormSq (matVecMul S η) ≤ vecNormSq η := by
        linarith
      _ ≤ vecDot η (matVecMul S η) := hcoercη

end PDE
