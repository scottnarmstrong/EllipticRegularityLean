module

public import EllipticRegularity.DeGiorgi.OneStep.PowerFn

/-!
# Two-sided power functions

`C¹` functions with compactly supported derivative agreeing with `t ↦ t ^ s` on `[δ, M]`.
-/

@[expose] public section

namespace PDE.DGNMOneStep

open Real

variable {δ : ℝ}

/-- The upper cutoff, equal to `1` on `(-∞, M + 1/2]` and to `0` on `[M + 1, ∞)`. -/
noncomputable def upperCut (M y : ℝ) : ℝ := Real.smoothTransition (2 * (M + 1 - y))

theorem upperCut_contDiff (M : ℝ) : ContDiff ℝ 1 (upperCut M) := by
  unfold upperCut
  exact (Real.smoothTransition.contDiff (n := 1)).comp (by fun_prop)

theorem upperCut_eq_one {M y : ℝ} (hy : y ≤ M + 1 / 2) : upperCut M y = 1 := by
  unfold upperCut
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem upperCut_eq_zero {M y : ℝ} (hy : M + 1 ≤ y) : upperCut M y = 0 := by
  unfold upperCut
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- Two-sided power function: `C¹`, bounded derivative, `G t = t ^ s` on `[δ, M]`. -/
theorem exists_powerFn_twoSided (hδ : 0 < δ) {M : ℝ} (hM : δ ≤ M) (s : ℝ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv G t| ≤ B) ∧
      (∀ t, 0 ≤ G t) ∧
      ∀ t, δ ≤ t → t ≤ M → G t = t ^ s ∧ deriv G t = s * t ^ (s - 1) := by
  set G : ℝ → ℝ := fun t => upperCut M (powBase δ t) * powBase δ t ^ s with hG
  have hcd : ContDiff ℝ 1 G :=
    ((upperCut_contDiff M).comp (powBase_contDiff)).mul
      ((powBase_contDiff (δ := δ)).rpow_const_of_ne (fun t => (powBase_pos hδ t).ne'))
  refine ⟨G, hcd, ?_, ?_, ?_⟩
  · have hcont : Continuous (deriv G) := hcd.continuous_deriv le_rfl
    have hsupp : HasCompactSupport (deriv G) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := δ / 2) (b := M + 1)) ?_
      intro t ht
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · have : G =ᶠ[nhds t] (fun _ => G (δ / 2)) := by
          filter_upwards [gt_mem_nhds h] with x hx
          simp only [hG, powBase_eq_of_ge hδ hx.le, powBase_eq_of_ge hδ (le_refl (δ / 2))]
        rw [this.deriv_eq]; simp
      · have : G =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
          filter_upwards [lt_mem_nhds h] with x hx
          have h1 : powBase δ x = x := powBase_eq_of_le hδ (by linarith)
          simp only [hG, h1, upperCut_eq_zero hx.le, zero_mul]
        rw [this.deriv_eq]; simp
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
    exact ⟨max C 0, le_max_right _ _, fun t => (by simpa using hC t : |deriv G t| ≤ C).trans (le_max_left _ _)⟩
  · intro t
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.rpow_nonneg (powBase_pos hδ t).le _)
  · intro t ht1 ht2
    have h34 : 3 * δ / 4 < t := by linarith
    have heq : G =ᶠ[nhds t] (fun x => x ^ s) := by
      filter_upwards [lt_mem_nhds h34, gt_mem_nhds (show t < M + 1 / 2 by linarith)] with x hx hx'
      have h1 : powBase δ x = x := powBase_eq_of_le hδ hx.le
      simp only [hG, h1, upperCut_eq_one hx'.le, one_mul]
    refine ⟨?_, ?_⟩
    · have := heq.eq_of_nhds
      simpa using this
    · rw [heq.deriv_eq, Real.deriv_rpow_const]

end PDE.DGNMOneStep
