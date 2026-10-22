module

public import EllipticRegularity.Guerra.Symmetrize.Basic

/-!
# Quadratic bounds for the symmetrization formula
-/

@[expose] public section

open scoped BigOperators

namespace PDE.GuerraSymmetrizeProof

variable {d : ℕ}

lemma vecNormSq_eq_dot (x : Vec d) : vecNormSq x = vecDot x x := rfl

/-- Two-sided bounds for the quadratic form of `form σ e z`. -/
lemma quad_bounds {k σ : ℝ} {e z : Vec d} (hk : 1 ≤ k) (hσ : k⁻¹ ≤ σ)
    (he : vecDot e e = 1) (hez : vecDot e z = 0)
    (hZ : σ ^ 2 + vecDot z z ≤ k * σ) (ξ : Vec d) :
    (2 * k)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (form σ e z) ξ) ∧
      vecDot ξ (matVecMul (form σ e z) ξ) ≤ 2 * k * vecNormSq ξ := by
  have hk0 : 0 < k := by linarith
  have hσ0 : 0 < σ := lt_of_lt_of_le (inv_pos.mpr hk0) hσ
  rw [vecDot_form]
  set a := vecDot ξ e with ha
  set b := vecDot ξ z with hb
  set N := vecNormSq ξ with hN
  set Z := vecDot z z with hZdef
  have hze : vecDot z e = 0 := by rw [vecDot_comm]; exact hez
  -- w = ξ - a e
  set w : Vec d := ξ - a • e with hw
  have hwe : vecDot w e = 0 := by
    rw [hw, vecDot_sub_left, vecDot_smul_left, he]
    have : vecDot ξ e = a := rfl
    rw [this]; ring
  have hww : vecDot w w = N - a ^ 2 := by
    rw [hw]
    simp only [vecDot_sub_left, vecDot_sub_right, vecDot_smul_left, vecDot_smul_right, he]
    have h1 : vecDot ξ ξ = N := rfl
    have h2 : vecDot ξ e = a := rfl
    have h3 : vecDot e ξ = a := by rw [vecDot_comm]
    rw [h1, h2, h3]; ring
  have hwz : vecDot w z = b := by
    rw [hw, vecDot_sub_left, vecDot_smul_left, hez]; ring
  have hW : 0 ≤ N - a ^ 2 := by rw [← hww]; exact vecNormSq_nonneg w
  have hbz : b ^ 2 ≤ (N - a ^ 2) * Z := by
    have := sq_vecDot_le_vecNormSq_mul_vecNormSq w z
    rw [hwz] at this
    simpa [vecNormSq_eq_dot, hww] using this
  have hsq : 0 ≤ σ ^ 2 * (N - a ^ 2) - 2 * σ * a * b + a ^ 2 * Z := by
    have h := vecNormSq_nonneg (σ • w - a • z)
    rw [vecNormSq_eq_dot] at h
    simp only [vecDot_sub_left, vecDot_sub_right, vecDot_smul_left, vecDot_smul_right] at h
    rw [hww, hwz, vecDot_comm z w, hwz] at h
    have hZ' : vecDot z z = Z := rfl
    rw [hZ'] at h
    linarith [h]
  have hNa : a ^ 2 ≤ N := by linarith
  have hkey : σ * (σ * N + 2 * (a * b) + 2 / σ * b ^ 2) = σ ^ 2 * N + 2 * σ * a * b + 2 * b ^ 2 := by
    field_simp
  constructor
  · -- lower bound
    have h1 : σ * (σ * N / 2) ≤ σ * (σ * N + 2 * (a * b) + 2 / σ * b ^ 2) := by
      rw [hkey]
      linarith [sq_nonneg (2 * b + σ * a), mul_le_mul_of_nonneg_left hNa (sq_nonneg σ)]
    have h2 : σ * N / 2 ≤ σ * N + 2 * (a * b) + 2 / σ * b ^ 2 :=
      le_of_mul_le_mul_left h1 hσ0
    have hN0 : 0 ≤ N := vecNormSq_nonneg ξ
    have h3 : (2 * k)⁻¹ ≤ σ / 2 := by
      have : (2 * k)⁻¹ = k⁻¹ / 2 := by field_simp
      rw [this]; linarith
    linarith [mul_le_mul_of_nonneg_right h3 hN0]
  · -- upper bound
    have h1 : σ * (σ * N + 2 * (a * b) + 2 / σ * b ^ 2) ≤ σ * (2 * k * N) := by
      rw [hkey]
      have hkσ : 0 ≤ k * σ := by positivity
      have e1 : 2 * b ^ 2 ≤ 2 * ((N - a ^ 2) * Z) := by linarith
      have e2 : (a ^ 2 + 2 * (N - a ^ 2)) * (σ ^ 2 + Z) ≤ (a ^ 2 + 2 * (N - a ^ 2)) * (k * σ) :=
        mul_le_mul_of_nonneg_left hZ (by nlinarith)
      nlinarith [e1, e2, hsq]
    exact le_of_mul_le_mul_left h1 hσ0

end PDE.GuerraSymmetrizeProof
