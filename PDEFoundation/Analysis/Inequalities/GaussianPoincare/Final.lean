module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Main

/-!
# The Gaussian Poincaré inequality: final statement
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

theorem hfun_zero {t : ℝ} (ht : 0 < t) (u : Vec d → ℝ) :
    hfun t u 0 = ∫ x : Vec d, u x ^ 2 * heat d t x := by
  unfold hfun
  have h : ∀ p : Vec d × Vec d, u p.1 * u (zc 0 p) * pairHeat d t p =
      (u p.1 ^ 2 * heat d t p.1) * heat d t p.2 := by
    intro p
    simp only [zc, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, pairHeat]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h)]
  have := integral_prod_mul (μ := (volume : Measure (Vec d))) (ν := (volume : Measure (Vec d)))
    (fun x => u x ^ 2 * heat d t x) (heat d t)
  rw [show (∫ p : Vec d × Vec d, (u p.1 ^ 2 * heat d t p.1) * heat d t p.2) = _ from this,
    integral_heat ht, mul_one]

theorem hfun_pi_div_two {t : ℝ} (u : Vec d → ℝ) :
    hfun t u (Real.pi / 2) = (∫ x : Vec d, u x * heat d t x) ^ 2 := by
  unfold hfun
  have h : ∀ p : Vec d × Vec d, u p.1 * u (zc (Real.pi / 2) p) * pairHeat d t p =
      (u p.1 * heat d t p.1) * (u p.2 * heat d t p.2) := by
    intro p
    simp only [zc, Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, zero_add,
      pairHeat]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h)]
  have := integral_prod_mul (μ := (volume : Measure (Vec d))) (ν := (volume : Measure (Vec d)))
    (fun x => u x * heat d t x) (fun x => u x * heat d t x)
  rw [show (∫ p : Vec d × Vec d, (u p.1 * heat d t p.1) * (u p.2 * heat d t p.2)) = _ from this,
    sq]

/-- The variance bound in terms of the product-kernel interpolation. -/
theorem variance_le {t : ℝ} (ht : 0 < t) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    hfun t u 0 - hfun t u (Real.pi / 2) ≤
      2 * t * ∫ x : Vec d, vecNormSq (classicalGradient u x) * heat d t x := by
  set A := ∫ x : Vec d, vecNormSq (classicalGradient u x) * heat d t x with hA
  set Gf : ℝ → ℝ := fun φ => hfun t u φ - 2 * t * A * Real.cos φ with hGf
  have hder : ∀ φ, HasDerivAt Gf
      ((∫ p : Vec d × Vec d, u p.1 * fderiv ℝ u (zc φ p) (wc φ p) * pairHeat d t p) +
        2 * t * A * Real.sin φ) φ := by
    intro φ
    have h1 := hasDerivAt_hfun ht hu hc φ
    have h2 := ((Real.hasDerivAt_cos φ).const_mul (2 * t * A))
    have := h1.sub h2
    convert this using 1
    ring
  have hmono : MonotoneOn Gf (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.2 fun φ => (hder φ).continuousAt).continuousOn
      (fun φ _ => (hder φ).differentiableAt.differentiableWithinAt) ?_
    intro φ hφ
    rw [interior_Icc] at hφ
    rw [(hder φ).deriv, integral_deriv_form ht hu hc φ]
    have hsin : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi hφ.1.le (by linarith [hφ.2, Real.pi_pos])
    have hcr := cross_term_le ht hu hc hφ.1.le hφ.2.le
    nlinarith [mul_nonneg ht.le hsin]
  have := hmono (Set.left_mem_Icc.2 (by positivity)) (Set.right_mem_Icc.2 (by positivity))
    (by positivity)
  simp only [hGf, Real.cos_zero, Real.cos_pi_div_two] at this
  linarith


/-- The Gaussian Poincaré inequality (Proposition 1.21), with the heat kernel
`Φ(t,x) = (4πt)^{-d/2} exp(-|x|²/(4t))`. -/
theorem gaussian_poincare_full (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (ht : 0 < t) (u : Vec d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    (∫ x, u x ^ 2 * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) -
        (∫ x, u x * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) ^ 2 ≤
      2 * t * ∫ x, vecEuclideanNorm (classicalGradient u x) ^ 2 *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t))) := by
  have _ := hd
  have h := variance_le ht hu hc
  rw [hfun_zero ht, hfun_pi_div_two] at h
  have e : ∀ x : Vec d, vecEuclideanNorm (classicalGradient u x) ^ 2 = vecNormSq (classicalGradient u x) :=
    fun x => Real.sq_sqrt (vecNormSq_nonneg _)
  simp only [e]
  exact h

end PDE.GaussianPoincare
