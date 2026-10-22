module

public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Ambient.MatAppend

/-!
# Ellipticity of block diagonal appended matrices

The block diagonal append operation preserves nonsymmetric ellipticity with the
same lower and inverse-coercivity constants.
-/

@[expose] public section

namespace PDE

/-- Matrix multiplication is componentwise on block diagonal appended
matrices. -/
theorem matAppend_mul {m n : ℕ} (A C : Mat m) (B D : Mat n) :
    matAppend A B * matAppend C D = matAppend (A * C) (B * D) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_add]

/-- Appending identity matrices gives the identity matrix. -/
theorem matAppend_one_one (m n : ℕ) :
    matAppend (1 : Mat m) (1 : Mat n) = (1 : Mat (m + n)) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Matrix.one_apply]
    · simp [Matrix.one_apply]
      intro h
      have := congrArg finSumFinEquiv.symm h
      simp at this
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Matrix.one_apply]
      intro h
      have := congrArg finSumFinEquiv.symm h
      simp at this
    · simp [Matrix.one_apply]

/-- The nonsingular inverse of an appended block diagonal matrix is the append
of the two nonsingular inverses. -/
theorem matAppend_nonsing_inv {m n : ℕ} (A : Mat m) (B : Mat n)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (matAppend A B)⁻¹ = matAppend A⁻¹ B⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [matAppend_mul, Matrix.nonsing_inv_mul A hA,
    Matrix.nonsing_inv_mul B hB, matAppend_one_one]

/-- Appending two elliptic matrices with the same constants preserves those
ellipticity constants. -/
theorem IsEllipticMatrix.matAppend {m n : ℕ} {lam Lam : ℝ}
    {A : Mat m} {B : Mat n} (hA : IsEllipticMatrix lam Lam A)
    (hB : IsEllipticMatrix lam Lam B) :
    IsEllipticMatrix lam Lam (matAppend A B) := by
  have hdetA : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  have hdetB : IsUnit B.det := isUnit_det_of_isEllipticMatrix hB
  refine ⟨hA.lam_pos, hA.lam_le_Lam, ?_, ?_⟩
  · intro ξ
    let x : Vec m := (vecAppendEquiv m n ξ).1
    let y : Vec n := (vecAppendEquiv m n ξ).2
    have hξ : ξ = (vecAppendEquiv m n).symm (x, y) := by
      exact ((vecAppendEquiv m n).symm_apply_apply ξ).symm
    rw [hξ, vecNormSq_vecAppendEquiv_symm]
    change lam * (vecNormSq x + vecNormSq y) ≤
      vecDot ((vecAppendEquiv m n).symm (x, y))
        ((_root_.PDE.matAppend A B).mulVec ((vecAppendEquiv m n).symm (x, y)))
    rw [matAppend_mulVec_vecAppendEquiv_symm,
      vecDot_vecAppendEquiv_symm]
    calc
      lam * (vecNormSq x + vecNormSq y) =
          lam * vecNormSq x + lam * vecNormSq y := by ring
      _ ≤ vecDot x (A.mulVec x) + vecDot y (B.mulVec y) :=
        add_le_add (hA.coercive x) (hB.coercive y)
  · intro ξ
    let x : Vec m := (vecAppendEquiv m n ξ).1
    let y : Vec n := (vecAppendEquiv m n ξ).2
    have hξ : ξ = (vecAppendEquiv m n).symm (x, y) := by
      exact ((vecAppendEquiv m n).symm_apply_apply ξ).symm
    rw [matAppend_nonsing_inv A B hdetA hdetB, hξ,
      vecNormSq_vecAppendEquiv_symm]
    change Lam⁻¹ * (vecNormSq x + vecNormSq y) ≤
      vecDot ((vecAppendEquiv m n).symm (x, y))
        ((_root_.PDE.matAppend A⁻¹ B⁻¹).mulVec ((vecAppendEquiv m n).symm (x, y)))
    rw [matAppend_mulVec_vecAppendEquiv_symm,
      vecDot_vecAppendEquiv_symm]
    calc
      Lam⁻¹ * (vecNormSq x + vecNormSq y) =
          Lam⁻¹ * vecNormSq x + Lam⁻¹ * vecNormSq y := by ring
      _ ≤ vecDot x (A⁻¹.mulVec x) + vecDot y (B⁻¹.mulVec y) :=
        add_le_add (hA.inverse_coercive x) (hB.inverse_coercive y)

end PDE
