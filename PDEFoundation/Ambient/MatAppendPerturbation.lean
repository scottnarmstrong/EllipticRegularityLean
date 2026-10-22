module

public import PDEFoundation.Ambient.MatAppend
public import PDEFoundation.Ambient.MatrixPerturbation

@[expose] public section

namespace PDE

private theorem vecEuclideanNorm_append_zero {m n : ℕ} (x : Vec m) :
    vecEuclideanNorm ((vecAppendEquiv m n).symm (x, (0 : Vec n))) =
      vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  rw [vecNormSq_vecAppendEquiv_symm]
  simp [vecNormSq, vecDot]

private theorem matAppend_sub_same {m n : ℕ} (A B : Mat m) (C : Mat n) :
    matAppend A C - matAppend B C = matAppend (A - B) (0 : Mat n) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

/-- Appending the same coefficient block preserves the exact Euclidean
perturbation bound. -/
theorem isMatrixPerturbationLE_matAppend_same_iff
    {m n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (A B : Mat m) (C : Mat n) :
    IsMatrixPerturbationLE δ (matAppend A C) (matAppend B C) ↔
      IsMatrixPerturbationLE δ A B := by
  constructor
  · intro h x
    have hx := h ((vecAppendEquiv m n).symm (x, (0 : Vec n)))
    change vecEuclideanNorm
      ((matAppend A C - matAppend B C).mulVec ((vecAppendEquiv m n).symm (x, 0))) ≤
        δ * vecEuclideanNorm ((vecAppendEquiv m n).symm (x, 0)) at hx
    rw [matAppend_sub_same, matAppend_mulVec_vecAppendEquiv_symm, Matrix.zero_mulVec,
      vecEuclideanNorm_append_zero, vecEuclideanNorm_append_zero] at hx
    exact hx
  · intro h z
    let x := (vecAppendEquiv m n z).1
    let y := (vecAppendEquiv m n z).2
    have hz : z = (vecAppendEquiv m n).symm (x, y) := by
      exact ((vecAppendEquiv m n).symm_apply_apply z).symm
    have hnorm : vecEuclideanNorm x ≤ vecEuclideanNorm z := by
      apply Real.sqrt_le_sqrt
      rw [vecNormSq_vecAppendEquiv m n z]
      exact le_add_of_nonneg_right (vecNormSq_nonneg _)
    change vecEuclideanNorm ((matAppend A C - matAppend B C).mulVec z) ≤
      δ * vecEuclideanNorm z
    rw [hz, matAppend_sub_same, matAppend_mulVec_vecAppendEquiv_symm,
      Matrix.zero_mulVec, vecEuclideanNorm_append_zero]
    exact (h x).trans (mul_le_mul_of_nonneg_left (by simpa only [hz] using hnorm) hδ)

end PDE
