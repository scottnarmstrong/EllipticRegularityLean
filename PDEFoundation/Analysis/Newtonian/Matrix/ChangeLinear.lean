module

public import PDEFoundation.Analysis.Newtonian.Defs
import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Linear algebra for the change of variables `x = S y` with `S Sᵀ = M`

For a symmetric elliptic matrix `M` we produce an invertible `S` with `S Sᵀ = M` and record the
algebraic identities used to reduce `div (M ∇ ·)` to the Laplacian: `matVecMul` is the matrix
action, `M⁻¹ = (S⁻¹)ᵀ S⁻¹`, `det M = (det S)²` and `|S⁻¹ z|² = zᵀ M⁻¹ z`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

theorem vecDot_eq_dotProduct (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem matVecMul_matVecMul (A B : Mat d) (x : Vec d) :
    matVecMul A (matVecMul B x) = matVecMul (A * B) x := by
  simp only [matVecMul_eq_mulVec, Matrix.mulVec_mulVec]

theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  simp only [matVecMul_eq_mulVec, Matrix.one_mulVec]

theorem vecDot_matVecMul_left (A : Mat d) (x y : Vec d) :
    vecDot (matVecMul A x) y = vecDot x (matVecMul Aᵀ y) := by
  simp only [matVecMul_eq_mulVec, vecDot_eq_dotProduct, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem vecNormSq_pos {x : Vec d} (hx : x ≠ 0) : 0 < vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hi' : x i ≠ 0 := hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ _, by positivity⟩

/-- A symmetric matrix with the ellipticity inequalities is positive definite. -/
theorem posDef_of_ellipticity {Λ : ℝ} (hΛ : 0 < Λ) {M : Mat d} (hMsymm : Matrix.IsSymm M)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ) : Matrix.PosDef M := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.2 hMsymm) ?_
  intro x hx
  have h1 := (hM x).1
  have h2 : 0 < Λ⁻¹ * vecNormSq x := mul_pos (inv_pos.2 hΛ) (vecNormSq_pos hx)
  simpa [star_trivial, matVecMul_eq_mulVec, vecDot_eq_dotProduct] using lt_of_lt_of_le h2 h1

/-- Factorization `M = S Sᵀ` with `S` of nonzero determinant. -/
theorem exists_factor {M : Mat d} (hM : Matrix.PosDef M) : ∃ S : Mat d, S * Sᵀ = M ∧ S.det ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := by
    open scoped MatrixOrder in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hS : a.transpose * (a.transpose)ᵀ = M := by
    simpa [Matrix.star_eq_conjTranspose] using ha.symm
  refine ⟨a.transpose, hS, fun h0 => ?_⟩
  have := hM.det_pos
  rw [← hS, Matrix.det_mul, h0, zero_mul] at this
  exact lt_irrefl _ this

section Algebra

variable {M S : Mat d}

theorem det_eq_sq (hS : S * Sᵀ = M) : M.det = S.det ^ 2 := by
  rw [← hS, Matrix.det_mul, Matrix.det_transpose, sq]

theorem sqrt_det_eq_abs (hS : S * Sᵀ = M) : Real.sqrt M.det = |S.det| := by
  rw [det_eq_sq hS, Real.sqrt_sq_eq_abs]

theorem mul_inv_self (hdet : S.det ≠ 0) : S * S⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)

theorem inv_mul_self (hdet : S.det ≠ 0) : S⁻¹ * S = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)

theorem inv_eq_transpose_mul (hS : S * Sᵀ = M) :
    M⁻¹ = (S⁻¹)ᵀ * S⁻¹ := by
  rw [← hS, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv]

theorem vecNormSq_inv_matVecMul (hS : S * Sᵀ = M) (z : Vec d) :
    vecNormSq (matVecMul S⁻¹ z) = vecDot z (matVecMul M⁻¹ z) := by
  unfold vecNormSq
  rw [vecDot_matVecMul_left, matVecMul_matVecMul, ← inv_eq_transpose_mul hS]

end Algebra

end MatChange

end PDE
