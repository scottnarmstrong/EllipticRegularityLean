module

public import EllipticRegularity.Ch4.Examples.LocalmaxCalc

/-!
# The subsolution of Proposition 4.12
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.Ch4Examples

open MeasureTheory Filter

/-- The subsolution `u = exp(x_d²/2 - s/(d-1))` with constant diagonal coefficients. -/
theorem localmax_subsolution (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val + 1 = d then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
            Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
              x i ^ 2) / ((d : ℝ) - 1))) ∧
        u.grad = classicalGradient u.toFun ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  set l : Fin d := ⟨d - 1, by omega⟩ with hl
  have hl1 : l.val + 1 = d := by simp [hl]; omega
  set c : ℝ := ((d - 1 : ℝ))⁻¹ with hc
  let w : Fin d → ℝ := fun i => if l = i then Λ else 1
  have hwi : ∀ i : Fin d, (if i.val + 1 = d then Λ else 1) = w i := by
    intro i
    have : (i.val + 1 = d) ↔ (l = i) := by
      rw [Fin.ext_iff, hl]; simp only; omega
    simp only [w, this]
  have hw : ∀ i, 1 ≤ w i ∧ w i ≤ Λ := by
    intro i
    by_cases h : l = i
    · simp [w, h, hΛ]
    · simp [w, h, hΛ]
  set φ := phiLM Λ c l with hφ
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_phiLM hΛ0 c l
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.exp (φ x)) := Real.contDiff_exp.comp hφs
  refine ⟨Matrix.diagonal w, fun i j => by simp [Matrix.diagonal_apply, hwi], 
    isEllipticMatrix_diagonal w Λ hΛ hw, ?_⟩
  let u : H1Function (euclideanBall (0 : Vec d) 1) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_euclideanBall 0 one_pos)
      (f := fun x => Real.exp (φ x))
      (hsmooth.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top))
  refine ⟨u, ?_, rfl, hsmooth, fun x => Real.exp_pos _, ?_⟩
  · intro x
    change Real.exp (φ x) = _
    rw [hφ]
    unfold phiLM Sf qf
    congr 1
    rw [Finset.sum_filter]
    simp only [tq, hc, div_eq_mul_inv]
    have : ∀ i : Fin d, (if i.val + 1 < d then (1 : ℝ) else 0) * x i ^ 2 =
        if i.val + 1 < d then x i ^ 2 else 0 := by
      intro i; split_ifs <;> simp
    simp only [this]
    ring
  · intro ψ hψ hψc hψ0
    change ∫ x, vecDot (matVecMul (Matrix.diagonal w)
      (fun i => fderiv ℝ (fun x => Real.exp (φ x)) x (basisVec i)))
      (fun i => fderiv ℝ ψ x (basisVec i)) ≤ 0
    rw [integral_flux_diag w _ (fun i j => by simp [Matrix.diagonal_apply]) hsmooth hψ hψc]
    rw [neg_nonpos]
    refine integral_nonneg fun x => mul_nonneg ?_ (hψ0 x)
    have := sum_weighted_nonneg hΛ hd l hl1 x
    have h2 : ∑ i, w i * D i (D i fun x => Real.exp (φ x)) x =
        Real.exp (φ x) * ∑ i, w i * (D i φ x ^ 2 + D i (D i φ) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [DD_exp i hφs]
      ring
    rw [h2]
    exact mul_nonneg (Real.exp_pos _).le this

end PDE.Ch4Examples
