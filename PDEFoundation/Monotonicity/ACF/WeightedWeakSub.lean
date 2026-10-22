module

public import PDEFoundation.Monotonicity.ACF.WeightedWeakRadial
public import PDEFoundation.PDE.DGNM.ProductTest

/-!
# The weighted sub-mean inequality `∫ ψ |∇u|² ≤ ½ ∫ u² Δψ` for radial test functions

For `u ≥ 0` continuous, `H¹` and weakly subharmonic on `B_R`, and `ψ = Ψ(|x|²)` with `Ψ ≥ 0`
smooth and `Ψ = 0` on `[ρ², ∞)`, `ρ < R`:

`∫ Ψ(|x|²) |∇u|² ≤ ½ ∫ u² (2 d Ψ'(|x|²) + 4 |x|² Ψ''(|x|²))`.

The proof tests with `v = u` (`subharmonic_productTest`) and uses the radial integration by parts
for `u ∇u · ∇ψ`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem matVecMul_one_apply (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  classical
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem isEllipticMatrix_one : IsEllipticMatrix 1 1 (1 : Mat d) := by
  classical
  refine ⟨one_pos, le_rfl, ?_, ?_⟩
  · intro ξ
    rw [matVecMul_one_apply, one_mul]
    rfl
  · intro ξ
    simp only [inv_one, matVecMul_one_apply, one_mul]
    exact le_rfl

theorem vecDot_smul_right_acf (x y : Vec d) (c : ℝ) : vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem classicalGradient_radial {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x : Vec d) :
    classicalGradient (fun y => Ψ (vecNormSq y)) x = (2 * deriv Ψ (vecNormSq x)) • x := by
  funext i
  have hKd : HasDerivAt Ψ (deriv Ψ (vecNormSq x)) (vecNormSq x) :=
    ((hΨ.differentiable (by simp)) _).hasDerivAt
  have h1 : HasFDerivAt (fun y : Vec d => Ψ (vecNormSq y))
      (deriv Ψ (vecNormSq x) • vecNormSqFDeriv x) x :=
    hKd.comp_hasFDerivAt x (hasFDerivAt_vecNormSq x)
  rw [classicalGradient_apply, h1.fderiv]
  simp only [smul_apply, vecNormSqFDeriv_basisVec, smul_eq_mul, Pi.smul_apply]
  ring

/-- **Weighted sub-mean inequality.** -/
theorem weighted_sub_inequality {R : ℝ} (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hΨ0 : ∀ s, ρ ^ 2 ≤ s → Ψ s = 0) (hΨnn : ∀ s, 0 ≤ s → 0 ≤ Ψ s) :
    IntegrableOn (fun x => Ψ (vecNormSq x) * vecNormSq (u.grad x))
        (euclideanBall (0 : Vec d) R) ∧
      ∫ x in euclideanBall (0 : Vec d) R, Ψ (vecNormSq x) * vecNormSq (u.grad x) ≤
        (1 / 2) * ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
          (2 * d * deriv Ψ (vecNormSq x) +
            4 * vecNormSq x * deriv (deriv Ψ) (vecNormSq x)) := by
  have hR : 0 < R := hρ.trans hρR
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR
  set ψ : Vec d → ℝ := fun x => Ψ (vecNormSq x) with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hΨ.comp contDiff_vecNormSq
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_euclideanClosedBall (0 : Vec d) hρ.le) ?_
    intro x hx
    rw [mem_euclideanClosedBall_zero_iff, not_le] at hx
    exact hΨ0 _ hx.le
  have hψU : tsupport ψ ⊆ euclideanBall (0 : Vec d) R := by
    have : tsupport ψ ⊆ euclideanClosedBall (0 : Vec d) ρ := by
      refine closure_minimal ?_ ?_
      · intro x hx
        by_contra h
        rw [mem_euclideanClosedBall_zero_iff, not_le] at h
        exact hx (hΨ0 _ h.le)
      · have : euclideanClosedBall (0 : Vec d) ρ = {x | vecNormSq x ≤ ρ ^ 2} := by
          ext x; exact mem_euclideanClosedBall_zero_iff
        rw [this]
        exact isClosed_le continuous_vecNormSq continuous_const
    refine this.trans fun x hx => ?_
    rw [mem_euclideanClosedBall_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff]
    nlinarith
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => hΨnn _ (vecNormSq_nonneg x)
  have hae : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ u.toFun x := by
    rw [volumeOn, ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall hnonneg
  obtain ⟨h1, h2, h3⟩ := DGNM.subharmonic_productTest (a := fun _ => (1 : Mat d)) (Λ := 1) hU
    (fun _ _ => aemeasurable_const) (fun _ _ => isEllipticMatrix_one) hsub u hae hψ hψc hψU hψ0
  simp only [matVecMul_one_apply] at h1 h2 h3
  -- second term via radial integration by parts
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun s => 2 * deriv Ψ s) :=
    contDiff_const.mul (contDiff_infty_iff_deriv.mp hΨ).2
  set ρ₁ : ℝ := (ρ + R) / 2 with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁]; linarith
  have hρ₁R : ρ₁ < R := by rw [hρ₁]; linarith
  have hρρ₁ : ρ < ρ₁ := by rw [hρ₁]; linarith
  have hK0 : ∀ s, ρ₁ ^ 2 ≤ s → 2 * deriv Ψ s = 0 := by
    intro s hs
    have : ρ ^ 2 < s := lt_of_lt_of_le (by nlinarith) hs
    simp [deriv_eq_zero_of_support hΨ0 this]
  have hibp := integral_radial_ibp u hcont hK hρ₁pos hρ₁R hK0
  refine ⟨h1.congr_fun (fun x _ => ?_) hU.isOpen.measurableSet, ?_⟩
  · rfl
  · have hd2 : Differentiable ℝ (deriv Ψ) := (contDiff_infty_iff_deriv.mp hΨ).2.differentiable (by simp)
    have e2 : ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x * vecDot (u.grad x) (classicalGradient ψ x) =
        ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x * ((2 * deriv Ψ (vecNormSq x)) * vecDot x (u.grad x)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hψdef, classicalGradient_radial hΨ, vecDot_smul_right_acf]
      rw [vecDot_comm (u.grad x) x]
    have e3 : ∀ x : Vec d, deriv (fun s => 2 * deriv Ψ s) (vecNormSq x) =
        2 * deriv (deriv Ψ) (vecNormSq x) := fun x => deriv_const_mul _ (hd2 _)
    rw [e2, hibp] at h3
    simp only [e3] at h3
    have e4 : ∫ x in euclideanBall (0 : Vec d) R, ψ x * vecDot (u.grad x) (u.grad x) =
        ∫ x in euclideanBall (0 : Vec d) R, Ψ (vecNormSq x) * vecNormSq (u.grad x) := rfl
    rw [e4] at h3
    have e5 : ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
          (↑d * (2 * deriv Ψ (vecNormSq x)) + 2 * vecNormSq x * (2 * deriv (deriv Ψ) (vecNormSq x))) =
        ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
          (2 * d * deriv Ψ (vecNormSq x) + 4 * vecNormSq x * deriv (deriv Ψ) (vecNormSq x)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [e5] at h3
    linarith only [h3]

end

end PDE
