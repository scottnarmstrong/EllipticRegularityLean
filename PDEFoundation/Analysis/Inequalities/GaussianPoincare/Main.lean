module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Ibp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Gaussian Poincaré inequality

We prove `PDE.GaussianPoincare.gaussian_poincare_full` by Ornstein--Uhlenbeck-type interpolation
between two independent Gaussian vectors: with `h(φ) = E[u(X) u(cos φ X + sin φ Y)]` one has
`h'(φ) = -2t sin φ E[∇u(X)·∇u(Z_φ)]` by Gaussian integration by parts, and the rotation invariance
of the product Gaussian yields `h(0) - h(π/2) ≤ 2t E|∇u|²`.
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

theorem integral_deriv_form {t : ℝ} (ht : 0 < t) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) (φ : ℝ) :
    ∫ p : Vec d × Vec d, u p.1 * fderiv ℝ u (zc φ p) (wc φ p) * pairHeat d t p =
      -(2 * t * Real.sin φ) * ∫ p : Vec d × Vec d,
        vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) * pairHeat d t p := by
  obtain ⟨M, L, hM0, hL0, hM, hL⟩ := exists_bounds hu hc
  have hG : ∀ x i, |classicalGradient u x i| ≤ L := fun x i => abs_classicalGradient_le hL x i
  have e1 : ∀ p : Vec d × Vec d, u p.1 * fderiv ℝ u (zc φ p) (wc φ p) * pairHeat d t p =
      ∑ i, u p.1 * classicalGradient u (zc φ p) i * (wc φ p i * pairHeat d t p) := by
    intro p
    rw [fderiv_apply_eq_vecDot_classicalGradient]
    simp only [vecDot, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∀ p : Vec d × Vec d,
      vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) * pairHeat d t p =
      ∑ i, classicalGradient u p.1 i * classicalGradient u (zc φ p) i * pairHeat d t p := by
    intro p
    simp only [vecDot, Finset.sum_mul]
  have int1 : ∀ i : Fin d, Integrable (fun p : Vec d × Vec d =>
      u p.1 * classicalGradient u (zc φ p) i * (wc φ p i * pairHeat d t p)) := fun i =>
    integrable_bdd_mul_lin_pairHeat ht
      (h := fun p => u p.1 * classicalGradient u (zc φ p) i)
      ((hu.continuous.comp continuous_fst).mul
        ((continuous_classicalGradient_apply hu i).comp (continuous_zc φ)))
      (C := M * L) (fun p => by
        rw [abs_mul]
        exact mul_le_mul (hM _) (hG _ _) (abs_nonneg _) hM0)
      ((continuous_apply i).comp (continuous_wc φ)) (abs_wc_apply_le φ · i)
  have int2 : ∀ i : Fin d, Integrable (fun p : Vec d × Vec d =>
      classicalGradient u p.1 i * classicalGradient u (zc φ p) i * pairHeat d t p) := fun i =>
    integrable_bdd_mul_pairHeat ht
      (h := fun p => classicalGradient u p.1 i * classicalGradient u (zc φ p) i)
      (((continuous_classicalGradient_apply hu i).comp continuous_fst).mul
        ((continuous_classicalGradient_apply hu i).comp (continuous_zc φ)))
      (C := L * L) (fun p => by
        rw [abs_mul]
        exact mul_le_mul (hG _ _) (hG _ _) (abs_nonneg _) hL0)
  rw [integral_congr_ae (Filter.Eventually.of_forall e1),
    integral_congr_ae (Filter.Eventually.of_forall e2),
    integral_finsetSum _ fun i _ => int1 i, integral_finsetSum _ fun i _ => int2 i,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => ibp_coord ht hu hc φ i

/-- Gaussian second moment of the squared gradient. -/
theorem bound_vecNormSq_gradient {u : Vec d → ℝ} {L : ℝ} (hL : ∀ x, ‖fderiv ℝ u x‖ ≤ L)
    (x : Vec d) : vecNormSq (classicalGradient u x) ≤ d * L ^ 2 := by
  rw [vecNormSq_eq_sum_sq]
  calc ∑ i, classicalGradient u x i ^ 2 ≤ ∑ _i : Fin d, L ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have := abs_classicalGradient_le hL x i
          nlinarith [abs_nonneg (classicalGradient u x i), sq_abs (classicalGradient u x i)]
    _ = d * L ^ 2 := by simp

theorem cross_term_le {t : ℝ} (ht : 0 < t) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ Real.pi / 2) :
    ∫ p : Vec d × Vec d,
        vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) * pairHeat d t p ≤
      ∫ x : Vec d, vecNormSq (classicalGradient u x) * heat d t x := by
  obtain ⟨M, L, hM0, hL0, hM, hL⟩ := exists_bounds hu hc
  have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hφ1⟩
  have hcs : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  have hgc : Continuous fun x : Vec d => vecNormSq (classicalGradient u x) := by
    have h : (fun x : Vec d => vecNormSq (classicalGradient u x)) =
        fun x => ∑ i, classicalGradient u x i ^ 2 := funext fun x => vecNormSq_eq_sum_sq _
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_classicalGradient_apply hu i).pow 2
  have hgb := bound_vecNormSq_gradient hL
  have hnn : ∀ x : Vec d, 0 ≤ vecNormSq (classicalGradient u x) := fun x => vecNormSq_nonneg _
  have i1 : Integrable (fun p : Vec d × Vec d =>
      vecNormSq (classicalGradient u p.1) * pairHeat d t p) :=
    integrable_bdd_mul_pairHeat ht (hgc.comp continuous_fst) (C := d * L ^ 2) fun p => by
      rw [abs_of_nonneg (hnn _)]; exact hgb _
  have i2 : Integrable (fun p : Vec d × Vec d =>
      vecNormSq (classicalGradient u (zc φ p)) * pairHeat d t p) :=
    integrable_bdd_mul_pairHeat ht (hgc.comp (continuous_zc φ)) (C := d * L ^ 2) fun p => by
      rw [abs_of_nonneg (hnn _)]; exact hgb _
  have hcont : Continuous fun p : Vec d × Vec d =>
      vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) := by
    unfold vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_classicalGradient_apply hu i).comp continuous_fst).mul
        ((continuous_classicalGradient_apply hu i).comp (continuous_zc φ))
  have i0 : Integrable (fun p : Vec d × Vec d =>
      vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) * pairHeat d t p) :=
    integrable_bdd_mul_pairHeat ht hcont (C := d * L ^ 2) fun p => by
      have := abs_vecDot_le_add_halves_vecNormSq (classicalGradient u p.1)
        (classicalGradient u (zc φ p))
      have h1 := hgb p.1
      have h2 := hgb (zc φ p)
      linarith
  have hmono : ∫ p : Vec d × Vec d,
        vecDot (classicalGradient u p.1) (classicalGradient u (zc φ p)) * pairHeat d t p ≤
      ∫ p : Vec d × Vec d, (1 / 2 * (vecNormSq (classicalGradient u p.1) * pairHeat d t p) +
        1 / 2 * (vecNormSq (classicalGradient u (zc φ p)) * pairHeat d t p)) := by
    refine integral_mono i0 ((i1.const_mul _).add (i2.const_mul _)) fun p => ?_
    have := (abs_le.1 (abs_vecDot_le_add_halves_vecNormSq (classicalGradient u p.1)
        (classicalGradient u (zc φ p)))).2
    have hp := pairHeat_nonneg ht p
    nlinarith
  have hA1 : ∫ p : Vec d × Vec d, vecNormSq (classicalGradient u (zc φ p)) * pairHeat d t p =
      ∫ x : Vec d, vecNormSq (classicalGradient u x) * heat d t x :=
    integral_comp_rot_pairHeat ht hcs (by linarith) (fun x => vecNormSq (classicalGradient u x))
  have hA0 : ∫ p : Vec d × Vec d, vecNormSq (classicalGradient u p.1) * pairHeat d t p =
      ∫ x : Vec d, vecNormSq (classicalGradient u x) * heat d t x := by
    have := integral_comp_rot_pairHeat ht (c := 1) (s := 0) (by norm_num) (by norm_num)
      (fun x => vecNormSq (classicalGradient u x))
    simpa using this
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, hA0,
    hA1]
  ring

end PDE.GaussianPoincare
