module

public import EllipticRegularity.Guerra.Field.Basic

/-!
# Guerra sharpness: action, inverse and coercivity of the matrix field `B`

For `x ≠ 0` write `ξ = s ω + w`.
Then `B ξ = (b s + Y·w) ω + w` and `B⁻¹ ξ = b⁻¹ (s - Y·w) ω + w`, `B` is invertible with
explicit inverse, and both quadratic forms are coercive whenever `|h| ≤ 10γ`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-! ### Linear-algebra plumbing -/

theorem matVecMul_eq_mulVec (A : Mat d) (x : Vec d) : matVecMul A x = A.mulVec x := rfl

theorem matVecMul_add' (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  simp only [matVecMul_eq_mulVec, Matrix.add_mulVec]

theorem matVecMul_smul' (c : ℝ) (A : Mat d) (x : Vec d) :
    matVecMul (c • A) x = c • matVecMul A x := by
  simp only [matVecMul_eq_mulVec, Matrix.smul_mulVec]

theorem matVecMul_sub' (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  simp only [matVecMul_eq_mulVec, Matrix.sub_mulVec]

theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  simp only [matVecMul_eq_mulVec, Matrix.one_mulVec]

theorem matVecMul_vecMulVec (a c ξ : Vec d) :
    matVecMul (Matrix.vecMulVec a c) ξ = vecDot c ξ • a := by
  funext i
  simp [matVecMul, Matrix.vecMulVec, vecDot, Finset.mul_sum, mul_comm, mul_left_comm]

theorem vecDot_add_smul_right (ξ a b : Vec d) (c : ℝ) :
    vecDot ξ (a + c • b) = vecDot ξ a + c * vecDot ξ b := by
  rw [vecDot_add_right, vecDot_smul_right]

/-! ### Action -/

/-- `B ξ = ξ + ((b-1)(ω·ξ) + Y·ξ) ω`, that is `(b s + Y·w) ω + w`. -/
theorem matVecMul_fieldMatrix (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x ξ : Vec d) :
    matVecMul (fieldMatrix γ h j x) ξ =
      ξ + ((bcoef γ - 1) * vecDot (omega x) ξ + vecDot (yvec h j x) ξ) • omega x := by
  unfold fieldMatrix
  rw [matVecMul_add', matVecMul_add', matVecMul_one', matVecMul_smul', matVecMul_vecMulVec,
    matVecMul_vecMulVec, add_smul, smul_smul]
  abel

theorem fieldMatrix_zero (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) :
    fieldMatrix γ h j (0 : Vec d) = (1 : Mat d) := by
  simp [fieldMatrix, omega_zero]

/-! ### The inverse -/

/-- The explicit inverse `1 + (b⁻¹-1) ω⊗ω - b⁻¹ ω⊗Y`. -/
def fieldMatrixInv (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) : Mat d :=
  (1 : Mat d) + ((bcoef γ)⁻¹ - 1) • Matrix.vecMulVec (omega x) (omega x) -
    (bcoef γ)⁻¹ • Matrix.vecMulVec (omega x) (yvec h j x)

private theorem mul_inv_aux (p p' c : ℝ) (a y : Vec d) (haa : vecDot a a = 1)
    (hya : vecDot y a = 0) (h1 : p + p' + p * p' = 0)
    (h2 : 1 + c + p * c = 0) :
    ((1 : Mat d) + p • Matrix.vecMulVec a a + Matrix.vecMulVec a y) *
      ((1 : Mat d) + p' • Matrix.vecMulVec a a + c • Matrix.vecMulVec a y) = 1 := by
  ext i k
  have haa' : a ⬝ᵥ a = 1 := haa
  have hya' : y ⬝ᵥ a = 0 := hya
  have e1 : (Matrix.vecMulVec a a * Matrix.vecMulVec a a) = Matrix.vecMulVec a a := by
    rw [Matrix.vecMulVec_mul_vecMulVec, haa', one_smul]
  have e2 : (Matrix.vecMulVec a a * Matrix.vecMulVec a y) = Matrix.vecMulVec a y := by
    rw [Matrix.vecMulVec_mul_vecMulVec, haa', one_smul]
  have e3 : (Matrix.vecMulVec a y * Matrix.vecMulVec a a) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hya', zero_smul]; ext i k; simp [Matrix.vecMulVec_apply]
  have e4 : (Matrix.vecMulVec a y * Matrix.vecMulVec a y) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hya', zero_smul]; ext i k; simp [Matrix.vecMulVec_apply]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, e1, e2, e3,
    e4, smul_zero, add_zero]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Matrix.one_apply]
  linear_combination (a i * a k) * h1 + (a i * y k) * h2

theorem fieldMatrix_mul_inv {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) :
    fieldMatrix γ h j x * fieldMatrixInv γ h j x = 1 := by
  have hb : bcoef γ ≠ 0 := by unfold bcoef; positivity
  by_cases hx : x = 0
  · subst hx; simp [fieldMatrix, fieldMatrixInv, omega_zero]
  · have := mul_inv_aux (d := d) (bcoef γ - 1) ((bcoef γ)⁻¹ - 1) (-(bcoef γ)⁻¹) (omega x)
      (yvec h j x) (vecNormSq_omega hx) (vecDot_yvec_omega hx h j)
      (by field_simp; ring) (by field_simp; ring)
    have e : fieldMatrixInv γ h j x = (1 : Mat d) + ((bcoef γ)⁻¹ - 1) •
        Matrix.vecMulVec (omega x) (omega x) +
        (-(bcoef γ)⁻¹) • Matrix.vecMulVec (omega x) (yvec h j x) := by
      unfold fieldMatrixInv; rw [neg_smul, sub_eq_add_neg]
    rw [e]; exact this

theorem fieldMatrix_isUnit_det {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) :
    IsUnit (fieldMatrix γ h j x).det :=
  Matrix.isUnit_det_of_right_inverse (fieldMatrix_mul_inv hγ h j x)

/-- The matrix inverse of `B(x)` is `1 + (b⁻¹-1) ω⊗ω - b⁻¹ ω⊗Y`
(also at `x = 0`, where it is `1`). -/
theorem fieldMatrix_inv {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) :
    (fieldMatrix γ h j x)⁻¹ = fieldMatrixInv γ h j x :=
  Matrix.inv_eq_right_inv (fieldMatrix_mul_inv hγ h j x)

theorem matVecMul_fieldMatrixInv (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x ξ : Vec d) :
    matVecMul (fieldMatrixInv γ h j x) ξ =
      ξ + (((bcoef γ)⁻¹ - 1) * vecDot (omega x) ξ - (bcoef γ)⁻¹ * vecDot (yvec h j x) ξ) •
        omega x := by
  unfold fieldMatrixInv
  rw [sub_eq_add_neg, matVecMul_add', matVecMul_add', matVecMul_one', matVecMul_smul',
    ← neg_smul, matVecMul_smul', matVecMul_vecMulVec, matVecMul_vecMulVec, smul_smul, smul_smul,
    add_assoc, ← add_smul]
  congr 2
  ring

/-! ### Quadratic forms -/

theorem quad_fieldMatrix (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x ξ : Vec d) :
    vecDot ξ (matVecMul (fieldMatrix γ h j x) ξ) =
      vecNormSq ξ + (bcoef γ - 1) * vecDot (omega x) ξ ^ 2 +
        vecDot (omega x) ξ * vecDot (yvec h j x) ξ := by
  rw [matVecMul_fieldMatrix, vecDot_add_right, vecDot_smul_right, vecDot_comm ξ (omega x)]
  change vecNormSq ξ + _ = _
  ring

theorem quad_fieldMatrixInv (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x ξ : Vec d) :
    vecDot ξ (matVecMul (fieldMatrixInv γ h j x) ξ) =
      vecNormSq ξ + ((bcoef γ)⁻¹ - 1) * vecDot (omega x) ξ ^ 2 -
        (bcoef γ)⁻¹ * (vecDot (omega x) ξ * vecDot (yvec h j x) ξ) := by
  rw [matVecMul_fieldMatrixInv, vecDot_add_right, vecDot_smul_right, vecDot_comm ξ (omega x)]
  change vecNormSq ξ + _ = _
  ring

/-- Cauchy-type bound `|z| ≤ (A + W)/4` from `z² ≤ A W / 4`. -/
theorem abs_le_quarter_of_sq_le {A W z : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hz : z ^ 2 ≤ A * W / 4) : |z| ≤ (A + W) / 4 := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg (A - W)]

theorem split_nonneg (x ξ : Vec d) : 0 ≤ vecNormSq ξ - vecDot (omega x) ξ ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    have : vecDot (omega (0 : Vec d)) ξ = 0 := by rw [omega_zero]; simp [vecDot]
    rw [this]; simpa using vecNormSq_nonneg ξ
  · set s := vecDot (omega x) ξ
    have hω := vecNormSq_omega hx
    have hsω : vecDot ξ (omega x) = s := by rw [vecDot_comm]
    have : vecNormSq (ξ - s • omega x) = vecNormSq ξ - s ^ 2 := by
      rw [vecNormSq, vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_smul_left,
        vecDot_smul_left, vecDot_smul_right, vecDot_smul_right, hω, hsω, vecDot_self_eq]
      ring
    rw [← this]; exact vecNormSq_nonneg _

/-- For `x ≠ 0`, `(Y·ξ)² ≤ (b/4) (|ξ|² - (ω·ξ)²)`, and `|ξ|² - (ω·ξ)² = |w|² ≥ 0`. -/
theorem tangential_bound {γ : ℝ} {h : ℝ → ℝ} (j : Fin d) {x : Vec d} (hx : x ≠ 0)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    0 ≤ vecNormSq ξ - vecDot (omega x) ξ ^ 2 ∧
      vecDot (yvec h j x) ξ ^ 2 ≤ bcoef γ / 4 * (vecNormSq ξ - vecDot (omega x) ξ ^ 2) := by
  set s := vecDot (omega x) ξ with hs
  set w := ξ - s • omega x with hw
  have hω := vecNormSq_omega hx
  have hsω : vecDot ξ (omega x) = s := by rw [vecDot_comm]
  have hww : vecNormSq w = vecNormSq ξ - s ^ 2 := by
    rw [vecNormSq, hw, vecDot_sub_left, vecDot_sub_right, vecDot_sub_right, vecDot_smul_left,
      vecDot_smul_left, vecDot_smul_right, vecDot_smul_right, hω, hsω, vecDot_self_eq]
    ring
  have hYw : vecDot (yvec h j x) w = vecDot (yvec h j x) ξ := by
    rw [hw, vecDot_sub_right, vecDot_smul_right, vecDot_yvec_omega hx]; ring
  refine ⟨by rw [← hww]; exact vecNormSq_nonneg w, ?_⟩
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (yvec h j x) w
  have hY := vecDot_yvec_yvec_le hx h j hh
  rw [hYw, hww] at hcs
  have hW : 0 ≤ vecNormSq ξ - s ^ 2 := by rw [← hww]; exact vecNormSq_nonneg w
  calc _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul_of_nonneg_right hY hW

/-- Coercivity of `B` in the split form `ξ·Bξ ≥ (b s² + |w|²)/2`. -/
theorem quad_fieldMatrix_ge {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    (bcoef γ * vecDot (omega x) ξ ^ 2 + (vecNormSq ξ - vecDot (omega x) ξ ^ 2)) / 2 ≤
      vecDot ξ (matVecMul (fieldMatrix γ h j x) ξ) := by
  have hb : 0 < bcoef γ := by unfold bcoef; positivity
  rw [quad_fieldMatrix]
  by_cases hx : x = 0
  · subst hx
    have : vecDot (omega (0 : Vec d)) ξ = 0 := by
      rw [omega_zero]; simp [vecDot]
    rw [this]
    have := vecNormSq_nonneg ξ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      zero_add, add_zero]
    linarith
  · obtain ⟨hW, hy⟩ := tangential_bound j hx hh ξ
    set s := vecDot (omega x) ξ
    set y := vecDot (yvec h j x) ξ
    set W := vecNormSq ξ - s ^ 2 with hWdef
    have hz : (s * y) ^ 2 ≤ (bcoef γ * s ^ 2) * W / 4 := by
      have := mul_le_mul_of_nonneg_left hy (sq_nonneg s)
      nlinarith
    have := abs_le_quarter_of_sq_le (mul_nonneg hb.le (sq_nonneg s)) hW hz
    have h2 := (abs_le.mp this).1
    have h3 : vecNormSq ξ = s ^ 2 + W := by rw [hWdef]; ring
    rw [h3]
    have : 0 ≤ bcoef γ * s ^ 2 := mul_nonneg hb.le (sq_nonneg s)
    nlinarith

/-- Coercivity of `B⁻¹` in the split form `ξ·B⁻¹ξ ≥ (b⁻¹ s² + |w|²)/2`. -/
theorem quad_fieldMatrixInv_ge {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    ((bcoef γ)⁻¹ * vecDot (omega x) ξ ^ 2 + (vecNormSq ξ - vecDot (omega x) ξ ^ 2)) / 2 ≤
      vecDot ξ (matVecMul (fieldMatrixInv γ h j x) ξ) := by
  have hb : 0 < bcoef γ := by unfold bcoef; positivity
  have hbi : 0 < (bcoef γ)⁻¹ := inv_pos.mpr hb
  rw [quad_fieldMatrixInv]
  by_cases hx : x = 0
  · subst hx
    have : vecDot (omega (0 : Vec d)) ξ = 0 := by
      rw [omega_zero]; simp [vecDot]
    rw [this]
    have := vecNormSq_nonneg ξ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
      zero_add, add_zero, zero_mul]
    linarith
  · obtain ⟨hW, hy⟩ := tangential_bound j hx hh ξ
    set s := vecDot (omega x) ξ
    set y := vecDot (yvec h j x) ξ
    set W := vecNormSq ξ - s ^ 2 with hWdef
    have hz : ((bcoef γ)⁻¹ * (s * y)) ^ 2 ≤ ((bcoef γ)⁻¹ * s ^ 2) * W / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hy (sq_nonneg ((bcoef γ)⁻¹ * s))
      have h2 : ((bcoef γ)⁻¹ * s) ^ 2 * (bcoef γ / 4 * W) = (bcoef γ)⁻¹ * s ^ 2 * W / 4 := by
        field_simp
      calc ((bcoef γ)⁻¹ * (s * y)) ^ 2 = ((bcoef γ)⁻¹ * s) ^ 2 * y ^ 2 := by ring
        _ ≤ _ := h1
        _ = _ := h2
    have := abs_le_quarter_of_sq_le (mul_nonneg hbi.le (sq_nonneg s)) hW hz
    have h2 := (abs_le.mp this).2
    have h3 : vecNormSq ξ = s ^ 2 + W := by rw [hWdef]; ring
    rw [h3]
    have : 0 ≤ (bcoef γ)⁻¹ * s ^ 2 := mul_nonneg hbi.le (sq_nonneg s)
    nlinarith

/-- `ξ·Bξ ≥ |ξ|²/2`. -/
theorem quad_fieldMatrix_ge_half {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    vecNormSq ξ / 2 ≤ vecDot ξ (matVecMul (fieldMatrix γ h j x) ξ) := by
  refine le_trans ?_ (quad_fieldMatrix_ge hγ j x hh ξ)
  have hb : 1 ≤ bcoef γ := by unfold bcoef; nlinarith
  have := sq_nonneg (vecDot (omega x) ξ)
  nlinarith

/-- `ξ·B⁻¹ξ ≥ b⁻¹|ξ|²/2`. -/
theorem quad_fieldMatrixInv_ge_half {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    (bcoef γ)⁻¹ * vecNormSq ξ / 2 ≤ vecDot ξ (matVecMul (fieldMatrixInv γ h j x) ξ) := by
  refine le_trans ?_ (quad_fieldMatrixInv_ge hγ j x hh ξ)
  have hb : 1 ≤ bcoef γ := by unfold bcoef; nlinarith
  have hbi : (bcoef γ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
  have hbp : 0 < (bcoef γ)⁻¹ := inv_pos.mpr (by linarith)
  have hW := split_nonneg x ξ
  have := sq_nonneg (vecDot (omega x) ξ)
  nlinarith

end

end PDE.Guerra
