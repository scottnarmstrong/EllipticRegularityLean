module

public import EllipticRegularity.Ch4.Examples.Basic

/-!
# The functions `G(x_a) cos(x_b)` with `G'' = k² G`

Used for `exp(√Λ x₁) cos x₂` and `cosh(√Λ x₁) cos x₂`.
-/

@[expose] public section

namespace PDE.Ch4Examples

open MeasureTheory

section CosProduct

variable {d : ℕ} (a b : Fin d) (G G1 : ℝ → ℝ) (k : ℝ)

/-- The product function `x ↦ G(x_a) cos(x_b)`. -/
noncomputable def cosProd (x : Vec d) : ℝ := G (x a) * Real.cos (x b)

variable {a b G G1 k}

theorem hasFDerivAt_cosProd (hG : ∀ t, HasDerivAt G (G1 t) t) (x : Vec d) :
    HasFDerivAt (cosProd a b G)
      ((Real.cos (x b) * G1 (x a)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a -
        (G (x a) * Real.sin (x b)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) b) x := by
  have h1 : HasFDerivAt (fun y : Vec d => G (y a))
      (G1 (x a) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a) x :=
    (hG (x a)).comp_hasFDerivAt x (hasFDerivAt_apply a x)
  have h2 : HasFDerivAt (fun y : Vec d => Real.cos (y b))
      ((-Real.sin (x b)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) b) x :=
    HasDerivAt.comp_hasFDerivAt (h₂ := Real.cos) (f := fun y : Vec d => y b) x
      (Real.hasDerivAt_cos (x b)) (hasFDerivAt_apply b x)
  refine HasFDerivAt.congr_fderiv (h1.mul h2) ?_
  ext v
  simp
  ring

theorem fderiv_cosProd_apply (hG : ∀ t, HasDerivAt G (G1 t) t) (x v : Vec d) :
    fderiv ℝ (cosProd a b G) x v =
      Real.cos (x b) * G1 (x a) * v a - G (x a) * Real.sin (x b) * v b := by
  rw [(hasFDerivAt_cosProd hG x).fderiv]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem contDiff_cosProd (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ContDiff ℝ (⊤ : ℕ∞) (cosProd a b G) := by
  unfold cosProd
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y a) := contDiff_apply ℝ ℝ a
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y b) := contDiff_apply ℝ ℝ b
  exact (hG.comp h1).mul (Real.contDiff_cos.comp h2)

/-- Second directional derivative of `G(x_a) cos(x_b)` in the direction `basisVec i`. -/
theorem D_D_cosProd (hG : ∀ t, HasDerivAt G (G1 t) t) (hG1 : ∀ t, HasDerivAt G1 (k ^ 2 * G t) t)
    (hab : a ≠ b) (i : Fin d) (x : Vec d) :
    D i (D i (cosProd a b G)) x =
      (if i = a then k ^ 2 * G (x a) * Real.cos (x b) else 0) -
        (if i = b then G (x a) * Real.cos (x b) else 0) := by
  have hfun : D i (cosProd a b G) = fun y : Vec d =>
      Real.cos (y b) * G1 (y a) * (if a = i then 1 else 0) -
        G (y a) * Real.sin (y b) * (if b = i then 1 else 0) := by
    funext y
    unfold D
    rw [fderiv_cosProd_apply hG]
    simp
  have hA : HasFDerivAt (fun y : Vec d => G1 (y a))
      ((k ^ 2 * G (x a)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a) x :=
    (hG1 (x a)).comp_hasFDerivAt x (hasFDerivAt_apply a x)
  have hB : HasFDerivAt (fun y : Vec d => G (y a))
      (G1 (x a) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a) x :=
    (hG (x a)).comp_hasFDerivAt x (hasFDerivAt_apply a x)
  have hC : HasFDerivAt (fun y : Vec d => Real.cos (y b))
      ((-Real.sin (x b)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) b) x :=
    HasDerivAt.comp_hasFDerivAt (h₂ := Real.cos) (f := fun y : Vec d => y b) x
      (Real.hasDerivAt_cos (x b)) (hasFDerivAt_apply b x)
  have hS : HasFDerivAt (fun y : Vec d => Real.sin (y b))
      (Real.cos (x b) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) b) x :=
    HasDerivAt.comp_hasFDerivAt (h₂ := Real.sin) (f := fun y : Vec d => y b) x
      (Real.hasDerivAt_sin (x b)) (hasFDerivAt_apply b x)
  have hT := (((hC.mul hA).mul_const (if a = i then (1 : ℝ) else 0)).sub
    ((hB.mul hS).mul_const (if b = i then (1 : ℝ) else 0)))
  change fderiv ℝ (D i (cosProd a b G)) x (basisVec i) = _
  rw [hfun]
  have hT2 : HasFDerivAt (fun y : Vec d =>
      Real.cos (y b) * G1 (y a) * (if a = i then (1 : ℝ) else 0) -
        G (y a) * Real.sin (y b) * (if b = i then (1 : ℝ) else 0)) _ x := hT
  rw [hT2.fderiv]
  simp only [sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    basisVec_apply]
  by_cases hia : i = a
  · have hib : i ≠ b := fun h => hab (hia ▸ h)
    subst hia
    simp [hib, hab.symm]
    ring
  · by_cases hib : i = b
    · subst hib
      simp [hia, Ne.symm hia]
    · simp [hia, hib, Ne.symm hia, Ne.symm hib]

/-- The equation `Σ w_i ∂_i∂_i (G(x_a) cos x_b) = 0` with `w_a = 1`, `w_b = k²`, `w_i = 1` else. -/
theorem sum_D_D_cosProd (hG : ∀ t, HasDerivAt G (G1 t) t) (hG1 : ∀ t, HasDerivAt G1 (k ^ 2 * G t) t)
    (hab : a ≠ b) (x : Vec d) :
    ∑ i, (if i = b then k ^ 2 else 1) * D i (D i (cosProd a b G)) x = 0 := by
  simp_rw [D_D_cosProd hG hG1 hab]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp [hab]
  ring

end CosProduct

/-- The shared construction: a constant diagonal matrix `diag(1, Λ, 1, …, 1)` and the smooth
function `G(x₀) cos x₁` packaged as an `H¹(B₁)` function, solving the equation on `ℝ^d`. -/
theorem cosProd_example (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) {G G1 : ℝ → ℝ}
    (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (Real.sqrt Λ ^ 2 * G t) t)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x = G (x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩)) ∧
        u.grad = classicalGradient u.toFun ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) := by
  set a : Fin d := ⟨0, by omega⟩ with ha
  set b : Fin d := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  let w : Fin d → ℝ := fun i => if i.val = 1 then Λ else 1
  have hw : ∀ i, 1 ≤ w i ∧ w i ≤ Λ := by
    intro i
    by_cases h : i.val = 1
    · simp [w, h, hΛ]
    · simp [w, h, hΛ]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (cosProd a b G) := contDiff_cosProd hGs
  refine ⟨Matrix.diagonal w, fun i j => by simp [Matrix.diagonal_apply, w],
    isEllipticMatrix_diagonal w Λ hΛ hw, ?_⟩
  let u : H1Function (euclideanBall (0 : Vec d) 1) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_euclideanBall 0 one_pos)
      (f := cosProd a b G)
      (hsmooth.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top))
  refine ⟨u, fun x => rfl, rfl, hsmooth, ?_⟩
  intro φ hφ hc
  change ∫ x, vecDot (matVecMul (Matrix.diagonal w) (fun i => fderiv ℝ (cosProd a b G) x (basisVec i)))
    (fun i => fderiv ℝ φ x (basisVec i)) = 0
  rw [integral_flux_diag w _ (fun i j => by simp [Matrix.diagonal_apply]) hsmooth hφ hc]
  have : ∀ x, ∑ i, w i * D i (D i (cosProd a b G)) x = 0 := by
    intro x
    have h0 := sum_D_D_cosProd (k := Real.sqrt Λ) hG hG1 hab x
    rw [Real.sq_sqrt (by linarith)] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, hb, Fin.ext_iff]
  simp [this]

end PDE.Ch4Examples
