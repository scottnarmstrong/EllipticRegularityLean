module

public import EllipticRegularity.Guerra.Field.Matrix

/-!
# Guerra sharpness: ellipticity of the coefficient fields

* `C = B/(20γ)` satisfies the hypotheses of the symmetrization lemma with `k = 40γ`;
* the nonsymmetric field `a = 2B` is elliptic with `Λ = (40γ)²`;
* for a symmetrizer `S` with the properties of `PDE.guerra_symmetrize` (a parameter; that
  lemma is proved elsewhere), the symmetric field `a = K S(C, ∇u)`, `K = 80γ`, is elliptic with
  `Λ = (80γ)²` and satisfies `a p = 4 B p` at `p = G x`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- `C = B/(20γ)`. -/
def cMatrix (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) : Mat d :=
  (20 * γ)⁻¹ • fieldMatrix γ h j x

/-- The nonsymmetric coefficient field `2B`. -/
def nonsymField (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (x : Vec d) : Mat d :=
  (2 : ℝ) • fieldMatrix γ h j x

/-- The symmetric coefficient field `a(x) = K S(B(x)/(20γ), G x)` for `x ≠ 0`, `a(0) = 2·1`,
where `K = 80γ`, `G` stands for `∇u` and `S` for the symmetrizer. -/
def symField (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (S : Mat d → Vec d → Mat d) (G : Vec d → Vec d)
    (x : Vec d) : Mat d :=
  if x = 0 then (2 : ℝ) • (1 : Mat d) else (80 * γ) • S (cMatrix γ h j x) (G x)

theorem symField_zero (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (S : Mat d → Vec d → Mat d)
    (G : Vec d → Vec d) : symField γ h j S G 0 = (2 : ℝ) • (1 : Mat d) := by
  simp [symField]

theorem symField_of_ne (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) (S : Mat d → Vec d → Mat d)
    (G : Vec d → Vec d) {x : Vec d} (hx : x ≠ 0) :
    symField γ h j S G x = (80 * γ) • S (cMatrix γ h j x) (G x) := by
  simp [symField, hx]

/-! ### Both coercivity bounds for `C` (`k = 40γ`) -/

theorem cMatrix_coercive {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    (40 * γ)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (cMatrix γ h j x) ξ) := by
  have hγ0 : 0 < γ := by linarith
  have := quad_fieldMatrix_ge_half hγ j x hh ξ
  unfold cMatrix
  rw [matVecMul_smul', vecDot_smul_right]
  have h2 : (40 * γ)⁻¹ = (20 * γ)⁻¹ * (1 / 2) := by field_simp; ring
  rw [h2, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem cMatrix_inv_coercive {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) (ξ : Vec d) :
    (40 * γ)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (cMatrix γ h j x)⁻¹ ξ) := by
  have hγ0 : 0 < γ := by linarith
  have hne : γ ≠ 0 := hγ0.ne'
  have := quad_fieldMatrixInv_ge_half hγ j x hh ξ
  have hinv : (cMatrix γ h j x)⁻¹ = (20 * γ) • fieldMatrixInv γ h j x := by
    unfold cMatrix
    rw [nonsing_inv_smul _ (by positivity) (fieldMatrix_isUnit_det hne h j x),
      fieldMatrix_inv hne, inv_inv]
  rw [hinv, matVecMul_smul', vecDot_smul_right]
  have h2 : (40 * γ)⁻¹ = (20 * γ) * ((bcoef γ)⁻¹ / 2) := by
    unfold bcoef; field_simp; ring
  rw [h2]
  calc 20 * γ * ((bcoef γ)⁻¹ / 2) * vecNormSq ξ = 20 * γ * ((bcoef γ)⁻¹ * vecNormSq ξ / 2) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-! ### The nonsymmetric field `2B` -/

theorem nonsymField_zero (γ : ℝ) (h : ℝ → ℝ) (j : Fin d) :
    nonsymField γ h j 0 = (2 : ℝ) • (1 : Mat d) := by
  simp [nonsymField, fieldMatrix_zero]

theorem isEllipticMatrix_nonsymField {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d) (x : Vec d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) :
    IsEllipticMatrix 1 ((40 * γ) ^ 2) (nonsymField γ h j x) := by
  have hγ0 : 0 < γ := by linarith
  have hne : γ ≠ 0 := hγ0.ne'
  have hb : (bcoef γ)⁻¹ * 4⁻¹ = ((40 * γ) ^ 2)⁻¹ := by unfold bcoef; field_simp; ring
  refine ⟨one_pos, by nlinarith, ?_, ?_⟩
  · intro ξ
    have := quad_fieldMatrix_ge_half hγ j x hh ξ
    unfold nonsymField
    rw [matVecMul_smul', vecDot_smul_right]
    linarith
  · intro ξ
    have := quad_fieldMatrixInv_ge_half hγ j x hh ξ
    have hinv : (nonsymField γ h j x)⁻¹ = (2 : ℝ)⁻¹ • fieldMatrixInv γ h j x := by
      unfold nonsymField
      rw [nonsing_inv_smul _ (by norm_num) (fieldMatrix_isUnit_det hne h j x),
        fieldMatrix_inv hne]
    rw [hinv, matVecMul_smul', vecDot_smul_right, ← hb]
    have hp : 0 ≤ (bcoef γ)⁻¹ * vecNormSq ξ :=
      mul_nonneg (inv_nonneg.mpr (by unfold bcoef; positivity)) (vecNormSq_nonneg ξ)
    nlinarith

/-! ### Symmetric fields from a symmetrizer -/

/-- A symmetric matrix with `lam |ξ|² ≤ ξ·Mξ ≤ Lam |ξ|²`, `0 < lam ≤ Lam` is elliptic in the
sense of `IsEllipticMatrix lam Lam` (the inverse bound by Cauchy-Schwarz for the positive
form `M`). -/
theorem isEllipticMatrix_of_symm_bounds {lam Lam : ℝ} {M : Mat d} (hlam : 0 < lam)
    (hle : lam ≤ Lam) (hsymm : ∀ i j, M i j = M j i)
    (hlo : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ))
    (hhi : ∀ ξ : Vec d, vecDot ξ (matVecMul M ξ) ≤ Lam * vecNormSq ξ) :
    IsEllipticMatrix lam Lam M := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
  refine ⟨hlam, hle, hlo, ?_⟩
  -- symmetry of the bilinear form
  have hbil : ∀ u v : Vec d, vecDot u (matVecMul M v) = vecDot (matVecMul M u) v := by
    intro u v
    simp only [vecDot, matVecMul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hsymm k i]; ring
  -- invertibility
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, hMv⟩
    have h0 : vecDot v (matVecMul M v) = 0 := by
      rw [matVecMul_eq_mulVec, hMv]; simp [vecDot]
    have := hlo v
    rw [h0] at this
    have hpos : 0 < vecNormSq v := by
      rcases (vecNormSq_nonneg v).lt_or_eq with h | h
      · exact h
      · exact absurd (vecNormSq_eq_zero h.symm) hv
    nlinarith
  intro ξ
  set y := matVecMul M⁻¹ ξ with hy
  have hMy : matVecMul M y = ξ := by
    rw [hy, matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
  have hyξ : vecDot ξ y = vecDot y (matVecMul M y) := by rw [hMy, vecDot_comm]
  have hyMξ : vecDot y (matVecMul M ξ) = vecNormSq ξ := by
    rw [hbil, hMy]; rfl
  -- positivity of the form
  have hQ : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul M v) := fun v =>
    le_trans (mul_nonneg hlam.le (vecNormSq_nonneg v)) (hlo v)
  -- discriminant
  have hdisc : ∀ t : ℝ, 0 ≤ vecDot ξ (matVecMul M ξ) * (t * t) + (2 * vecNormSq ξ) * t +
      vecDot y (matVecMul M y) := by
    intro t
    have h1 := hQ (y + t • ξ)
    have h2 : vecDot (y + t • ξ) (matVecMul M (y + t • ξ)) =
        vecDot y (matVecMul M y) + 2 * t * vecDot y (matVecMul M ξ) +
          t ^ 2 * vecDot ξ (matVecMul M ξ) := by
      have hm : matVecMul M (y + t • ξ) = matVecMul M y + t • matVecMul M ξ := by
        simp only [matVecMul_eq_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
      have f2 : vecDot ξ (matVecMul M y) = vecNormSq ξ := by rw [hMy]; rfl
      rw [hm, vecDot_add_left, vecDot_add_right, vecDot_add_right, vecDot_smul_left,
        vecDot_smul_right, vecDot_smul_right, vecDot_smul_left, hyMξ, f2]
      ring
    rw [h2, hyMξ] at h1
    nlinarith
  have hd := discrim_le_zero hdisc
  unfold discrim at hd
  have hcs : vecNormSq ξ ^ 2 ≤ vecDot y (matVecMul M y) * vecDot ξ (matVecMul M ξ) := by
    nlinarith
  rw [← hyξ] at hcs
  have hyy : vecDot ξ (matVecMul M⁻¹ ξ) = vecDot ξ y := rfl
  rw [hyy]
  rcases (vecNormSq_nonneg ξ).lt_or_eq with hpos | h0
  · have hup := hhi ξ
    have h3 : vecNormSq ξ ^ 2 ≤ vecDot ξ y * (Lam * vecNormSq ξ) := by
      have hy0 : 0 ≤ vecDot ξ y := by rw [hyξ]; exact hQ y
      calc _ ≤ _ := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_left hup hy0
    have h4 : vecNormSq ξ ≤ vecDot ξ y * Lam := by
      by_contra hcon
      have hcon := not_le.mp hcon
      nlinarith
    rw [inv_mul_le_iff₀ hLam]
    linarith
  · rw [← h0]; simp only [mul_zero]; rw [hyξ]; exact hQ y

/-- `S(C, p) p = C p` with `C = B/(20γ)` gives `K S(C,p) p = 4 B p` for `K = 80γ`. -/
theorem matVecMul_symField_self {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d)
    {S : Mat d → Vec d → Mat d} {G : Vec d → Vec d} {x : Vec d} (hx : x ≠ 0)
    (hSp : matVecMul (S (cMatrix γ h j x) (G x)) (G x) = matVecMul (cMatrix γ h j x) (G x)) :
    matVecMul (symField γ h j S G x) (G x) =
      (4 : ℝ) • matVecMul (fieldMatrix γ h j x) (G x) := by
  have hγ0 : 0 < γ := by linarith
  rw [symField_of_ne γ h j S G hx, matVecMul_smul', hSp]
  unfold cMatrix
  rw [matVecMul_smul', smul_smul]
  congr 1
  field_simp
  norm_num

/-- The symmetrizer interface (data of `PDE.guerra_symmetrize` for `k = 40γ`, used as a
hypothesis). -/
def IsSymmetrizer (k : ℝ) (S : Mat d → Vec d → Mat d) : Prop :=
  ∀ (C : Mat d) (p : Vec d),
    (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C ξ)) →
    (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C⁻¹ ξ)) →
    (∀ i j : Fin d, S C p i j = S C p j i) ∧
    matVecMul (S C p) p = matVecMul C p ∧
    (∀ ξ : Vec d, (2 * k)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (S C p) ξ)) ∧
    (∀ ξ : Vec d, vecDot ξ (matVecMul (S C p) ξ) ≤ 2 * k * vecNormSq ξ)

theorem symField_symm {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) {S : Mat d → Vec d → Mat d}
    (hS : IsSymmetrizer (40 * γ) S) (G : Vec d → Vec d) (x : Vec d) (i k : Fin d) :
    symField γ h j S G x i k = symField γ h j S G x k i := by
  by_cases hx : x = 0
  · subst hx
    rw [symField_zero]
    by_cases hik : i = k
    · subst hik; rfl
    · simp [hik, Ne.symm hik]
  · rw [symField_of_ne γ h j S G hx]
    have := (hS _ (G x) (cMatrix_coercive hγ j x hh) (cMatrix_inv_coercive hγ j x hh)).1 i k
    simp only [Matrix.smul_apply, smul_eq_mul, this]

theorem symField_apply_self {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) {S : Mat d → Vec d → Mat d}
    (hS : IsSymmetrizer (40 * γ) S) (G : Vec d → Vec d) {x : Vec d} (hx : x ≠ 0) :
    matVecMul (symField γ h j S G x) (G x) =
      (4 : ℝ) • matVecMul (fieldMatrix γ h j x) (G x) :=
  matVecMul_symField_self hγ j hx
    (hS _ (G x) (cMatrix_coercive hγ j x hh) (cMatrix_inv_coercive hγ j x hh)).2.1

/-- The symmetric field is uniformly elliptic with `λ = 1`, `Λ = (80γ)²` at every point
(with `a(0) = 2·1`). -/
theorem isEllipticMatrix_symField {γ : ℝ} (hγ : 1 ≤ γ) {h : ℝ → ℝ} (j : Fin d)
    (hh : ∀ t, |t| ≤ 1 → |h t| ≤ 10 * γ) {S : Mat d → Vec d → Mat d}
    (hS : IsSymmetrizer (40 * γ) S) (G : Vec d → Vec d) (x : Vec d) :
    IsEllipticMatrix 1 ((80 * γ) ^ 2) (symField γ h j S G x) := by
  have hγ0 : 0 < γ := by linarith
  refine isEllipticMatrix_of_symm_bounds one_pos (by nlinarith)
    (symField_symm hγ j hh hS G x) ?_ ?_
  · intro ξ
    by_cases hx : x = 0
    · subst hx
      rw [symField_zero, matVecMul_smul', matVecMul_one', vecDot_smul_right]
      change 1 * vecNormSq ξ ≤ 2 * vecNormSq ξ
      nlinarith [vecNormSq_nonneg ξ]
    · rw [symField_of_ne γ h j S G hx, matVecMul_smul', vecDot_smul_right]
      have := (hS _ (G x) (cMatrix_coercive hγ j x hh)
        (cMatrix_inv_coercive hγ j x hh)).2.2.1 ξ
      have h2 : (2 * (40 * γ))⁻¹ * (80 * γ) = 1 := by field_simp; norm_num
      calc 1 * vecNormSq ξ = (80 * γ) * ((2 * (40 * γ))⁻¹ * vecNormSq ξ) := by
            rw [← mul_assoc, mul_comm (80 * γ), h2]
        _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  · intro ξ
    by_cases hx : x = 0
    · subst hx
      rw [symField_zero, matVecMul_smul', matVecMul_one', vecDot_smul_right]
      change 2 * vecNormSq ξ ≤ (80 * γ) ^ 2 * vecNormSq ξ
      have h2 : 2 ≤ (80 * γ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2 (vecNormSq_nonneg ξ)]
    · rw [symField_of_ne γ h j S G hx, matVecMul_smul', vecDot_smul_right]
      have := (hS _ (G x) (cMatrix_coercive hγ j x hh)
        (cMatrix_inv_coercive hγ j x hh)).2.2.2 ξ
      calc (80 * γ) * _ ≤ (80 * γ) * (2 * (40 * γ) * vecNormSq ξ) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring

end

end PDE.Guerra
