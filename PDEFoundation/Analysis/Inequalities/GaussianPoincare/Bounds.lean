module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Rotation
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Bounds and integrability for compactly supported smooth test functions
-/

@[expose] public section

open MeasureTheory Real

namespace PDE.GaussianPoincare

variable {d : ℕ}

theorem norm_basisVec_le (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i <;> simp [basisVec_apply, h]

theorem contDiff_one_of_top {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiff ℝ 1 u :=
  hu.of_le (by exact_mod_cast le_top)

/-- Uniform bounds for a compactly supported smooth function. -/
theorem exists_bounds {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ (∀ x, |u x| ≤ M) ∧ (∀ x, ‖fderiv ℝ u x‖ ≤ L) := by
  have hu1 := contDiff_one_of_top hu
  obtain ⟨M, hM⟩ := hu.continuous.bounded_above_of_compact_support hc
  obtain ⟨L, hL⟩ := (hu1.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  exact ⟨M, L, (norm_nonneg _).trans (hM 0), (norm_nonneg _).trans (hL 0),
    fun x => by simpa using hM x, hL⟩

theorem abs_classicalGradient_le {u : Vec d → ℝ} {L : ℝ} (hL : ∀ x, ‖fderiv ℝ u x‖ ≤ L)
    (x : Vec d) (i : Fin d) : |classicalGradient u x i| ≤ L := by
  rw [classicalGradient_apply, ← Real.norm_eq_abs]
  refine ((fderiv ℝ u x).le_opNorm _).trans ?_
  have := hL x
  have h0 := norm_nonneg (fderiv ℝ u x)
  nlinarith [norm_basisVec_le i, norm_nonneg (basisVec i : Vec d)]

theorem continuous_classicalGradient_apply {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (i : Fin d) : Continuous fun x => classicalGradient u x i :=
  (continuous_apply i).comp (ContDiff.continuous_classicalGradient (contDiff_one_of_top hu))

/-- The rotated point. -/
noncomputable def zc (φ : ℝ) (p : Vec d × Vec d) : Vec d := Real.cos φ • p.1 + Real.sin φ • p.2

/-- The velocity of the rotated point. -/
noncomputable def wc (φ : ℝ) (p : Vec d × Vec d) : Vec d := -Real.sin φ • p.1 + Real.cos φ • p.2

theorem continuous_zc (φ : ℝ) : Continuous (zc φ : Vec d × Vec d → Vec d) := by
  unfold zc
  fun_prop

theorem continuous_wc (φ : ℝ) : Continuous (wc φ : Vec d × Vec d → Vec d) := by
  unfold wc
  fun_prop

theorem norm_wc_le (φ : ℝ) (p : Vec d × Vec d) : ‖wc φ p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  unfold wc
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  have h1 := Real.abs_sin_le_one φ
  have h2 := Real.abs_cos_le_one φ
  nlinarith [norm_nonneg p.1, norm_nonneg p.2, abs_nonneg (Real.sin φ), abs_nonneg (Real.cos φ)]

theorem abs_wc_apply_le (φ : ℝ) (p : Vec d × Vec d) (i : Fin d) :
    |wc φ p i| ≤ ‖p.1‖ + ‖p.2‖ := by
  have := (norm_le_pi_norm (wc φ p) i)
  rw [Real.norm_eq_abs] at this
  exact this.trans (norm_wc_le φ p)

/-- Bounded continuous functions times the product heat kernel are integrable. -/
theorem integrable_bdd_mul_pairHeat {t : ℝ} (ht : 0 < t) {h : Vec d × Vec d → ℝ}
    (hh : Continuous h) {C : ℝ} (hb : ∀ p, |h p| ≤ C) :
    Integrable (fun p : Vec d × Vec d => h p * pairHeat d t p) := by
  exact Integrable.bdd_mul (c := C) (integrable_pairHeat ht) hh.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa using hb p)

/-- Bounded continuous functions times a linearly growing weight times the product heat kernel. -/
theorem integrable_bdd_mul_lin_pairHeat {t : ℝ} (ht : 0 < t) {h q : Vec d × Vec d → ℝ}
    (hh : Continuous h) {C : ℝ} (hb : ∀ p, |h p| ≤ C) (hq : Continuous q)
    (hqb : ∀ p, |q p| ≤ ‖p.1‖ + ‖p.2‖) :
    Integrable (fun p : Vec d × Vec d => h p * (q p * pairHeat d t p)) := by
  have hqi : Integrable (fun p : Vec d × Vec d => q p * pairHeat d t p) := by
    refine Integrable.mono' (integrable_norm_mul_pairHeat (d := d) ht) ?_ ?_
    · exact (hq.mul (continuous_pairHeat t)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pairHeat_nonneg ht p)]
      exact mul_le_mul_of_nonneg_right (hqb p) (pairHeat_nonneg ht p)
  exact Integrable.bdd_mul (c := C) hqi hh.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa using hb p)

end PDE.GaussianPoincare
