module

public import PDEFoundation.Analysis.Newtonian.Matrix.ChangeLinear

/-!
# Operator-norm bounds for the factor `S` of an elliptic matrix

If `M = S Sᵀ` with `Λ⁻¹|ξ|² ≤ ξᵀMξ`, then `|S⁻¹ v| ≤ √Λ |v|` and `|(S⁻¹)ᵀ v| ≤ √Λ |v|`.
-/

@[expose] public section

open scoped Matrix

namespace PDE

namespace MatChange

variable {d : ℕ}

theorem le_sqrt_mul_of_sq_le {Λ a b : ℝ} (hΛ : 0 ≤ Λ) (hb : 0 ≤ b) (h : a ^ 2 ≤ Λ * b ^ 2)
    (ha : 0 ≤ a) : a ≤ Real.sqrt Λ * b := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (Λ * b ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt Λ * b := by rw [Real.sqrt_mul hΛ, Real.sqrt_sq hb]

theorem vecEuclideanNorm_inv_transpose_le {Λ : ℝ} (hΛ : 0 < Λ) {M S : Mat d} (hS : S * Sᵀ = M)
    (hdet : S.det ≠ 0)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ)) (v : Vec d) :
    vecEuclideanNorm (matVecMul (S⁻¹)ᵀ v) ≤ Real.sqrt Λ * vecEuclideanNorm v := by
  set w := matVecMul (S⁻¹)ᵀ v with hw
  have hSw : matVecMul Sᵀ w = v := by
    rw [hw, matVecMul_matVecMul, ← Matrix.transpose_mul, inv_mul_self hdet]
    simp [matVecMul_one]
  have h1 : vecDot w (matVecMul M w) = vecNormSq v := by
    rw [← hS, ← matVecMul_matVecMul]
    have := vecDot_matVecMul_left Sᵀ w (matVecMul Sᵀ w)
    rw [Matrix.transpose_transpose] at this
    rw [← this, hSw]
    rfl
  have h2 := hM w
  rw [h1] at h2
  have h3 : vecNormSq w ≤ Λ * vecNormSq v := by
    have := mul_le_mul_of_nonneg_left h2 hΛ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at this
  refine le_sqrt_mul_of_sq_le hΛ.le (vecEuclideanNorm_nonneg _) ?_ (vecEuclideanNorm_nonneg _)
  rw [vecEuclideanNorm_sq, vecEuclideanNorm_sq]
  exact h3

theorem vecEuclideanNorm_inv_le {Λ : ℝ} (hΛ : 0 < Λ) {M S : Mat d} (hS : S * Sᵀ = M)
    (hdet : S.det ≠ 0)
    (hM : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ)) (v : Vec d) :
    vecEuclideanNorm (matVecMul S⁻¹ v) ≤ Real.sqrt Λ * vecEuclideanNorm v := by
  set y := matVecMul S⁻¹ v with hy
  have hSy : matVecMul S y = v := by
    rw [hy, matVecMul_matVecMul, mul_inv_self hdet, matVecMul_one]
  have hSw : matVecMul Sᵀ (matVecMul (S⁻¹)ᵀ y) = y := by
    rw [matVecMul_matVecMul, ← Matrix.transpose_mul, inv_mul_self hdet]
    simp [matVecMul_one]
  have hT := vecEuclideanNorm_inv_transpose_le hΛ hS hdet hM y
  have h1 : vecNormSq y = vecDot v (matVecMul (S⁻¹)ᵀ y) := by
    rw [← hSy, vecDot_matVecMul_left, hSw]
    rfl
  have h2 : vecNormSq y ≤ vecEuclideanNorm v * (Real.sqrt Λ * vecEuclideanNorm y) := by
    calc vecNormSq y ≤ |vecDot v (matVecMul (S⁻¹)ᵀ y)| := h1 ▸ le_abs_self _
      _ ≤ vecEuclideanNorm v * vecEuclideanNorm (matVecMul (S⁻¹)ᵀ y) :=
          abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (vecEuclideanNorm_nonneg _)
  rw [← vecEuclideanNorm_sq] at h2
  by_cases h0 : vecEuclideanNorm y = 0
  · rw [h0]; exact mul_nonneg (Real.sqrt_nonneg _) (vecEuclideanNorm_nonneg _)
  · have hpos : 0 < vecEuclideanNorm y := lt_of_le_of_ne (vecEuclideanNorm_nonneg _) (Ne.symm h0)
    have : vecEuclideanNorm y * vecEuclideanNorm y ≤
        (Real.sqrt Λ * vecEuclideanNorm v) * vecEuclideanNorm y := by
      calc vecEuclideanNorm y * vecEuclideanNorm y = vecEuclideanNorm y ^ 2 := (sq _).symm
        _ ≤ _ := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos

end MatChange

end PDE
