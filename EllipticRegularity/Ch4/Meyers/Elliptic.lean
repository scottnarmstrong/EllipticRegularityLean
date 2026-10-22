module

public import EllipticRegularity.Ch4.Meyers.Profile

/-!
# Ellipticity of the coefficient field `I + (Λ - 1) q qᵀ / s`
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

variable {d : ℕ} {w : Fin d → ℝ}

/-- The matrix `I + c q qᵀ / s`. -/
noncomputable def qmat (q : Vec d) (s c : ℝ) : Mat d :=
  fun i j => (if i = j then 1 else 0) + c * q i * q j / s

theorem matVecMul_qmat (q ξ : Vec d) (s c : ℝ) (i : Fin d) :
    matVecMul (qmat q s c) ξ i = ξ i + c * q i / s * ∑ j, q j * ξ j := by
  simp only [matVecMul_apply, qmat, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecDot_matVecMul_qmat (q ξ : Vec d) (s c : ℝ) :
    vecDot ξ (matVecMul (qmat q s c) ξ) = vecNormSq ξ + c / s * (∑ j, q j * ξ j) ^ 2 := by
  have h : ∀ i, ξ i * matVecMul (qmat q s c) ξ i =
      ξ i ^ 2 + c / s * (∑ j, q j * ξ j) * (q i * ξ i) := by
    intro i; rw [matVecMul_qmat]; ring
  unfold vecDot
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, vecNormSq_eq_sum_sq]
  ring

theorem qmat_mul (q : Vec d) {s : ℝ} (hs : 0 < s) (hq : ∑ j, q j ^ 2 = s) (c c' : ℝ) :
    qmat q s c * qmat q s c' = qmat q s (c + c' + c * c') := by
  ext i k
  simp only [Matrix.mul_apply, qmat, add_mul, mul_add, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq']
  have h3 : ∑ j, c * q i * q j / s * (c' * q j * q k / s) = c * c' * q i * q k / s := by
    have : ∀ j, c * q i * q j / s * (c' * q j * q k / s) =
        c * c' * q i * q k / s ^ 2 * q j ^ 2 := by
      intro j; ring
    simp_rw [this]
    rw [← Finset.mul_sum, hq]
    field_simp
  rw [h3]
  ring

theorem qmat_zero_coeff (q : Vec d) (s : ℝ) : qmat q s 0 = 1 := by
  ext i j
  simp [qmat, Matrix.one_apply]

theorem isEllipticMatrix_qmat (q : Vec d) {s : ℝ} (hs : 0 < s) (hq : ∑ j, q j ^ 2 = s)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) : IsEllipticMatrix 1 Λ (qmat q s (Λ - 1)) := by
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨one_pos, hΛ, ?_, ?_⟩
  · intro ξ
    rw [vecDot_matVecMul_qmat, one_mul]
    have : 0 ≤ (Λ - 1) / s * (∑ j, q j * ξ j) ^ 2 :=
      mul_nonneg (div_nonneg (by linarith) hs.le) (sq_nonneg _)
    linarith
  · intro ξ
    have hinv : (qmat q s (Λ - 1))⁻¹ = qmat q s (Λ⁻¹ - 1) := by
      apply Matrix.inv_eq_right_inv
      rw [qmat_mul q hs hq]
      have : Λ - 1 + (Λ⁻¹ - 1) + (Λ - 1) * (Λ⁻¹ - 1) = 0 := by
        field_simp; ring
      rw [this, qmat_zero_coeff]
    rw [hinv, vecDot_matVecMul_qmat]
    have hcs : (∑ j, q j * ξ j) ^ 2 ≤ s * vecNormSq ξ := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ q ξ
      rw [hq] at this
      rw [vecNormSq_eq_sum_sq]
      exact this
    have hle : Λ⁻¹ - 1 ≤ 0 := by
      have : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
      linarith
    have h1 : (Λ⁻¹ - 1) * (s * vecNormSq ξ) ≤ (Λ⁻¹ - 1) * (∑ j, q j * ξ j) ^ 2 :=
      mul_le_mul_of_nonpos_left hcs hle
    have h2 : (Λ⁻¹ - 1) / s * (∑ j, q j * ξ j) ^ 2 ≥ (Λ⁻¹ - 1) * vecNormSq ξ := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hs]
      linarith
    linarith

theorem meyersCoeff_eq_qmat (w : Fin d → ℝ) (Λ : ℝ) (x : Vec d) :
    meyersCoeff w Λ x = qmat (fun j => w j * x j) (axisSq w x) (Λ - 1) := rfl

theorem meyersCoeff_of_axisSq_eq_zero (w : Fin d → ℝ) (Λ : ℝ) {x : Vec d}
    (hs : axisSq w x = 0) : meyersCoeff w Λ x = 1 := by
  ext i j
  simp [meyersCoeff, hs, Matrix.one_apply]

/-- Ellipticity of the coefficient field, at every point. -/
theorem isEllipticMatrix_meyersCoeff (hw : ∀ i, w i = 0 ∨ w i = 1) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (x : Vec d) : IsEllipticMatrix 1 Λ (meyersCoeff w Λ x) := by
  rcases (axisSq_nonneg hw x).eq_or_lt with hs | hs
  · rw [meyersCoeff_of_axisSq_eq_zero w Λ hs.symm]
    refine ⟨one_pos, hΛ, ?_, ?_⟩
    · intro ξ
      have : matVecMul (1 : Mat d) ξ = ξ := by
        funext i; simp [matVecMul, Matrix.one_apply]
      rw [this]; simp [vecNormSq]
    · intro ξ
      have : matVecMul ((1 : Mat d)⁻¹) ξ = ξ := by
        funext i; simp [matVecMul, Matrix.one_apply]
      rw [this]
      have h0 := vecNormSq_nonneg ξ
      have : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
      have h1 : vecDot ξ ξ = vecNormSq ξ := rfl
      rw [h1]
      nlinarith
  · rw [meyersCoeff_eq_qmat]
    exact isEllipticMatrix_qmat _ hs (sum_wx_sq hw x) hΛ

end PDE.Ch4Meyers
