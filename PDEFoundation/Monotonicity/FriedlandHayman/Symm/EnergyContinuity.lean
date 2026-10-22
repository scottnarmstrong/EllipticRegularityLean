module

public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Energy

/-!
# Friedland--Hayman: sup-norm continuity of the nonlocal energy

`nlEnergy ε` is locally Lipschitz, hence continuous, for the sup-norm topology on `C(Sph D, ℝ)`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace PDE.FHLane

noncomputable section

variable {D : ℕ}

namespace Symm

theorem nlEnergy_eq_prod (ε : ℝ) (g : C(Sph D, ℝ)) :
    nlEnergy ε g = ∫ p, kern ε g p.1 p.2 ∂((sphMeasure D).prod (sphMeasure D)) := by
  rw [integral_prod _ (integrable_of_bdd (measurable_kern ε g) (fun p => abs_kern_le ε g p.1 p.2))]
  rfl

theorem abs_kern_sub_le (ε : ℝ) (g₁ g₂ : C(Sph D, ℝ)) (x y : Sph D) :
    |kern ε g₁ x y - kern ε g₂ x y| ≤ 4 * dist g₁ g₂ * (‖g₁‖ + ‖g₂‖) := by
  unfold kern
  split_ifs
  · rw [sq_sub_sq, abs_mul]
    have h1 := ContinuousMap.dist_apply_le_dist (f := g₁) (g := g₂) x
    have h2 := ContinuousMap.dist_apply_le_dist (f := g₁) (g := g₂) y
    rw [Real.dist_eq] at h1 h2
    have h3 := abs_sub_le_two_norm g₁ x y
    have h4 := abs_sub_le_two_norm g₂ x y
    have hA : |g₁ x - g₁ y - (g₂ x - g₂ y)| ≤ 2 * dist g₁ g₂ := by
      rw [abs_le] at *
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hB : |g₁ x - g₁ y + (g₂ x - g₂ y)| ≤ 2 * (‖g₁‖ + ‖g₂‖) := by
      refine (abs_add_le _ _).trans ?_
      linarith
    calc _ ≤ 2 * (‖g₁‖ + ‖g₂‖) * (2 * dist g₁ g₂) :=
          mul_le_mul hB hA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [sub_zero, abs_zero]; positivity

theorem abs_nlEnergy_sub_le (ε : ℝ) (g₁ g₂ : C(Sph D, ℝ)) :
    |nlEnergy ε g₁ - nlEnergy ε g₂| ≤
      4 * dist g₁ g₂ * (‖g₁‖ + ‖g₂‖) * ((sphMeasure D).real univ * (sphMeasure D).real univ) := by
  rw [nlEnergy_eq_prod, nlEnergy_eq_prod,
    ← integral_sub (integrable_of_bdd (measurable_kern ε g₁) (fun p => abs_kern_le ε g₁ p.1 p.2))
      (integrable_of_bdd (measurable_kern ε g₂) (fun p => abs_kern_le ε g₂ p.1 p.2))]
  have := norm_integral_le_of_norm_le_const (μ := (sphMeasure D).prod (sphMeasure D))
    (f := fun p : Sph D × Sph D => kern ε g₁ p.1 p.2 - kern ε g₂ p.1 p.2)
    (C := 4 * dist g₁ g₂ * (‖g₁‖ + ‖g₂‖))
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using abs_kern_sub_le ε g₁ g₂ p.1 p.2)
  rw [Real.norm_eq_abs] at this
  convert this using 2
  simp [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]

end Symm

/-- The nonlocal energy is continuous for the sup-norm topology. -/
theorem continuous_nlEnergy (ε : ℝ) : Continuous (nlEnergy (D := D) ε) := by
  refine Metric.continuous_iff.2 fun g₀ ε' hε' => ?_
  set M : ℝ := (sphMeasure D).real univ with hM
  have hM0 : 0 ≤ M := measureReal_nonneg
  set L : ℝ := 4 * (2 * ‖g₀‖ + 1) * (M * M) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨min 1 (ε' / (L + 1)), by positivity, fun g hg => ?_⟩
  have hd1 : dist g g₀ < 1 := hg.trans_le (min_le_left _ _)
  have hd2 : dist g g₀ < ε' / (L + 1) := hg.trans_le (min_le_right _ _)
  have hn : ‖g‖ ≤ ‖g₀‖ + 1 := by
    have : ‖g‖ ≤ ‖g₀‖ + ‖g - g₀‖ := by simpa using norm_le_insert' g g₀
    rw [← dist_eq_norm] at this
    linarith
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (Symm.abs_nlEnergy_sub_le ε g g₀) ?_
  have hd0 := dist_nonneg (x := g) (y := g₀)
  have h1 : 4 * dist g g₀ * (‖g‖ + ‖g₀‖) * (M * M) ≤ L * dist g g₀ := by
    rw [hL]
    have : 0 ≤ M * M := mul_nonneg hM0 hM0
    nlinarith [norm_nonneg g, norm_nonneg g₀, mul_nonneg hd0 this]
  have h2 : dist g g₀ * (L + 1) < ε' := by
    rwa [lt_div_iff₀ (by positivity)] at hd2
  nlinarith

end

end PDE.FHLane
