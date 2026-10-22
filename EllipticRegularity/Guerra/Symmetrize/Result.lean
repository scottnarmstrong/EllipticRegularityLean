module

public import EllipticRegularity.Guerra.Symmetrize.Construction

/-!
# Symmetrization of a flux: the full statement

The statement of Lemma 4.31 (`PDE.guerra_symmetrize`), proved by the explicit
formula `A = σ Id + e ⊗ z + z ⊗ e + (2/σ) z ⊗ z` of the manuscript. This helper module is what
other Guerra modules import.
-/

@[expose] public section

open scoped BigOperators

namespace PDE.GuerraSymmetrizeProof

theorem symmetrizer_exists (d : ℕ) (k : ℝ) (hk : 1 ≤ k) :
    ∃ S : Mat d → Vec d → Mat d,
      (∀ i j : Fin d, Measurable
        (fun q : (Fin d → Fin d → ℝ) × Vec d => S (Matrix.of q.1) q.2 i j)) ∧
      ∀ (C : Mat d) (p : Vec d),
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C ξ)) →
        (∀ ξ : Vec d, k⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul C⁻¹ ξ)) →
        (∀ i j : Fin d, S C p i j = S C p j i) ∧
        matVecMul (S C p) p = matVecMul C p ∧
        (∀ ξ : Vec d, (2 * k)⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (S C p) ξ)) ∧
        (∀ ξ : Vec d, vecDot ξ (matVecMul (S C p) ξ) ≤ 2 * k * vecNormSq ξ) := by
  have hk0 : 0 < k := by linarith
  refine ⟨symS k, measurable_symS k, ?_⟩
  intro C p h1 h2
  by_cases hp : p = 0
  · subst hp
    have hS : symS k C 0 = Matrix.of fun i j => if i = j then k⁻¹ else 0 := by simp [symS]
    have hmul : ∀ ξ : Vec d, matVecMul (symS k C 0) ξ = k⁻¹ • ξ := by
      intro ξ
      funext i
      simp [hS, matVecMul]
    have hq : ∀ ξ : Vec d, vecDot ξ (matVecMul (symS k C 0) ξ) = k⁻¹ * vecNormSq ξ := by
      intro ξ
      rw [hmul, vecDot_smul_right]; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      rw [hS]
      simp only [Matrix.of_apply]
      by_cases h : i = j <;> simp [h, eq_comm]
    · have : ∀ A : Mat d, matVecMul A 0 = 0 := fun A => by funext i; simp [matVecMul]
      rw [this, this]
    · intro ξ
      rw [hq]
      have hN := vecNormSq_nonneg ξ
      have : (2 * k)⁻¹ ≤ k⁻¹ := by
        rw [mul_inv]; have := inv_pos.mpr hk0; nlinarith [inv_pos.mpr (two_pos : (0:ℝ) < 2)]
      nlinarith
    · intro ξ
      rw [hq]
      have hN := vecNormSq_nonneg ξ
      have : k⁻¹ ≤ 2 * k := by
        have h1 : k⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
        linarith
      nlinarith
  · set e := symE p with he_def
    have hNp : 0 < vecNormSq p :=
      lt_of_le_of_ne (vecNormSq_nonneg p) fun h => hp (vecNormSq_eq_zero h.symm)
    have hr : 0 < Real.sqrt (vecNormSq p) := Real.sqrt_pos.mpr hNp
    have hee : vecDot e e = 1 := by
      have : vecDot e e = ((Real.sqrt (vecNormSq p))⁻¹) ^ 2 * vecNormSq p := by
        rw [he_def, symE, vecDot_smul_left, vecDot_smul_right]
        rw [show vecDot p p = vecNormSq p from rfl]; ring
      rw [this, inv_pow, Real.sq_sqrt hNp.le]
      field_simp
    have hpe : p = Real.sqrt (vecNormSq p) • e := by
      rw [he_def, symE, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    set σ := symσ C p with hσdef
    set z := symZ C p with hzdef
    set c := matVecMul C e with hc
    have hσ' : σ = vecDot e c := rfl
    have hσk : k⁻¹ ≤ σ := by
      have := h1 e
      rw [show vecNormSq e = 1 from hee, mul_one] at this
      exact this
    have hσ0 : 0 < σ := lt_of_lt_of_le (inv_pos.mpr hk0) hσk
    -- invertibility
    have hunit : IsUnit C.det := by
      by_contra hn
      have h0 : C⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit C hn
      have := h2 e
      rw [h0, show vecNormSq e = 1 from hee] at this
      have hz0 : matVecMul (0 : Mat d) e = 0 := by funext i; simp [matVecMul]
      rw [hz0] at this
      have h3 : vecDot e (0 : Vec d) = 0 := by simp [vecDot]
      rw [h3] at this
      linarith [inv_pos.mpr hk0]
    have hinv : matVecMul C⁻¹ c = e := by
      rw [hc, matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul C hunit, Matrix.one_mulVec]
    have hcc : k⁻¹ * vecNormSq c ≤ σ := by
      have := h2 c
      rw [hinv, vecDot_comm] at this
      exact this
    have hce : vecDot c e = σ := by rw [vecDot_comm]; exact hσ'.symm
    have hez : vecDot e z = 0 := by
      rw [hzdef, symZ]
      change vecDot e (c - σ • e) = 0
      rw [vecDot_sub_right, vecDot_smul_right, hee, ← hσ']; ring
    have hZ : vecDot z z = vecNormSq c - σ ^ 2 := by
      change vecDot (c - σ • e) (c - σ • e) = _
      simp only [vecDot_sub_left, vecDot_sub_right, vecDot_smul_left, vecDot_smul_right, hee,
        hce, vecDot_comm e c]
      rw [vecNormSq_eq_dot]; ring
    have hZle : σ ^ 2 + vecDot z z ≤ k * σ := by
      rw [hZ]
      have : vecNormSq c ≤ k * σ := by
        have := mul_le_mul_of_nonneg_left hcc hk0.le
        rwa [← mul_assoc, mul_inv_cancel₀ hk0.ne', one_mul] at this
      linarith
    have hSp : symS k C p = form σ e z := by rw [symS, ite_eq_right hp]
    have hAe : matVecMul (form σ e z) e = c := by
      rw [form_apply]
      have hze : vecDot z e = 0 := by rw [vecDot_comm]; exact hez
      rw [hze, hee]
      change σ • e + (0:ℝ) • e + (1:ℝ) • (c - σ • e) + (2 / σ * 0) • (c - σ • e) = c
      module
    have hbd := quad_bounds hk hσk hee hez hZle
    refine ⟨?_, ?_, fun ξ => by rw [hSp]; exact (hbd ξ).1,
      fun ξ => by rw [hSp]; exact (hbd ξ).2⟩
    · intro i j
      rw [hSp]; exact form_symm σ e z i j
    · rw [hSp]
      have hmulsmul : ∀ (A : Mat d) (t : ℝ) (x : Vec d),
          matVecMul A (t • x) = t • matVecMul A x := by
        intro A t x
        rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec, Matrix.mulVec_smul]
      conv_lhs => rw [hpe]
      conv_rhs => rw [hpe]
      rw [hmulsmul, hmulsmul, hAe]

end PDE.GuerraSymmetrizeProof

