module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Bounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of the interpolation functional
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

/-- The interpolation functional `h(φ) = ∫∫ u(x) u(cos φ x + sin φ y) Φ(x) Φ(y)`. -/
noncomputable def hfun (t : ℝ) (u : Vec d → ℝ) (φ : ℝ) : ℝ :=
  ∫ p : Vec d × Vec d, u p.1 * u (zc φ p) * pairHeat d t p

theorem hasDerivAt_zc (φ : ℝ) (p : Vec d × Vec d) :
    HasDerivAt (fun φ => zc φ p) (wc φ p) φ := by
  unfold zc wc
  exact ((Real.hasDerivAt_cos φ).smul_const p.1).add ((Real.hasDerivAt_sin φ).smul_const p.2)

theorem hasDerivAt_hfun {t : ℝ} (ht : 0 < t) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) (φ₀ : ℝ) :
    HasDerivAt (hfun t u)
      (∫ p : Vec d × Vec d, u p.1 * fderiv ℝ u (zc φ₀ p) (wc φ₀ p) * pairHeat d t p) φ₀ := by
  obtain ⟨M, L, hM0, hL0, hM, hL⟩ := exists_bounds hu hc
  have hu1 := contDiff_one_of_top hu
  have hcont : ∀ φ, Continuous fun p : Vec d × Vec d => u p.1 * u (zc φ p) :=
    fun φ => (hu.continuous.comp continuous_fst).mul (hu.continuous.comp (continuous_zc φ))
  have hcontF : ∀ φ, Continuous fun p : Vec d × Vec d =>
      u p.1 * fderiv ℝ u (zc φ p) (wc φ p) :=
    fun φ => (hu.continuous.comp continuous_fst).mul
      (((hu1.continuous_fderiv (by simp)).comp (continuous_zc φ)).clm_apply (continuous_wc φ))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := Set.univ) (x₀ := φ₀)
    (F := fun φ (p : Vec d × Vec d) => u p.1 * u (zc φ p) * pairHeat d t p)
    (F' := fun φ (p : Vec d × Vec d) => u p.1 * fderiv ℝ u (zc φ p) (wc φ p) * pairHeat d t p)
    (bound := fun p => (M * L) * ((‖p.1‖ + ‖p.2‖) * pairHeat d t p)) Filter.univ_mem
    (Filter.Eventually.of_forall fun φ =>
      ((hcont φ).mul (continuous_pairHeat t)).aestronglyMeasurable)
    (integrable_bdd_mul_pairHeat ht (hcont φ₀) (C := M * M) fun p => by
      rw [abs_mul]
      exact mul_le_mul (hM _) (hM _) (abs_nonneg _) hM0)
    (((hcontF φ₀).mul (continuous_pairHeat t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p φ _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pairHeat_nonneg ht p)]
      have h1 : |fderiv ℝ u (zc φ p) (wc φ p)| ≤ L * (‖p.1‖ + ‖p.2‖) := by
        rw [← Real.norm_eq_abs]
        refine ((fderiv ℝ u (zc φ p)).le_opNorm _).trans ?_
        exact mul_le_mul (hL _) (norm_wc_le φ p) (norm_nonneg _) hL0
      have h2 : |u p.1| * |fderiv ℝ u (zc φ p) (wc φ p)| ≤ M * (L * (‖p.1‖ + ‖p.2‖)) :=
        mul_le_mul (hM _) h1 (abs_nonneg _) hM0
      calc _ ≤ M * (L * (‖p.1‖ + ‖p.2‖)) * pairHeat d t p :=
            mul_le_mul_of_nonneg_right h2 (pairHeat_nonneg ht p)
        _ = _ := by ring)
    ((integrable_norm_mul_pairHeat ht).const_mul _)
    (Filter.Eventually.of_forall fun p φ _ => by
      have h1 : HasDerivAt (fun φ => u (zc φ p)) (fderiv ℝ u (zc φ p) (wc φ p)) φ :=
        (hu.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt φ
          (hasDerivAt_zc φ p)
      exact (h1.const_mul (u p.1)).mul_const (pairHeat d t p))
  exact key.2

end PDE.GaussianPoincare
