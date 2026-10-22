/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyCutoff

/-! # Smooth time ramps -/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open Set

/-- Smooth ramp from `0` (for `τ ≤ α`) to `1` (for `τ ≥ β`). -/
noncomputable def upRamp (α β τ : ℝ) : ℝ := Real.smoothTransition ((τ - α) / (β - α))

/-- Smooth ramp from `1` (for `τ ≤ α`) to `0` (for `τ ≥ β`). -/
noncomputable def downRamp (α β τ : ℝ) : ℝ := Real.smoothTransition ((β - τ) / (β - α))

theorem upRamp_contDiff (α β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (upRamp α β) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem downRamp_contDiff (α β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (downRamp α β) :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem upRamp_nonneg (α β τ : ℝ) : 0 ≤ upRamp α β τ := Real.smoothTransition.nonneg _
theorem upRamp_le_one (α β τ : ℝ) : upRamp α β τ ≤ 1 := Real.smoothTransition.le_one _
theorem downRamp_nonneg (α β τ : ℝ) : 0 ≤ downRamp α β τ := Real.smoothTransition.nonneg _
theorem downRamp_le_one (α β τ : ℝ) : downRamp α β τ ≤ 1 := Real.smoothTransition.le_one _

theorem upRamp_eq_zero {α β τ : ℝ} (h : α < β) (hτ : τ ≤ α) : upRamp α β τ = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem upRamp_eq_one {α β τ : ℝ} (h : α < β) (hτ : β ≤ τ) : upRamp α β τ = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by linarith)).2 (by linarith))

theorem downRamp_eq_one {α β τ : ℝ} (h : α < β) (hτ : τ ≤ α) : downRamp α β τ = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by linarith)).2 (by linarith))

theorem downRamp_eq_zero {α β τ : ℝ} (h : α < β) (hτ : β ≤ τ) : downRamp α β τ = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- A universal bound for the derivative of the smooth transition profile. -/
theorem exists_deriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s, |deriv Real.smoothTransition s| ≤ B :=
  PDE.Parabolic.LocalMax.exists_abs_deriv_smoothTransition_le

theorem abs_deriv_upRamp_le {B : ℝ} (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) {α β : ℝ}
    (h : α < β) (τ : ℝ) : |deriv (upRamp α β) τ| ≤ B / (β - α) := by
  have h1 : HasDerivAt (fun t : ℝ => (t - α) / (β - α)) (1 / (β - α)) τ := by
    simpa using ((hasDerivAt_id τ).sub_const α).div_const (β - α)
  have h2 : HasDerivAt (upRamp α β)
      (deriv Real.smoothTransition ((τ - α) / (β - α)) * (1 / (β - α))) τ :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp τ h1
  have hpos : 0 < β - α := by linarith
  rw [h2.deriv, abs_mul, abs_of_pos (show 0 < 1 / (β - α) by positivity)]
  calc _ ≤ B * (1 / (β - α)) := mul_le_mul_of_nonneg_right (hB _) (by positivity)
    _ = _ := by ring

theorem abs_deriv_downRamp_le {B : ℝ} (hB : ∀ s, |deriv Real.smoothTransition s| ≤ B) {α β : ℝ}
    (h : α < β) (τ : ℝ) : |deriv (downRamp α β) τ| ≤ B / (β - α) := by
  have h1 : HasDerivAt (fun t : ℝ => (β - t) / (β - α)) (-1 / (β - α)) τ := by
    simpa using ((hasDerivAt_id τ).const_sub β).div_const (β - α)
  have h2 : HasDerivAt (downRamp α β)
      (deriv Real.smoothTransition ((β - τ) / (β - α)) * (-1 / (β - α))) τ :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp τ h1
  have hpos : 0 < β - α := by linarith
  rw [h2.deriv, abs_mul, show -1 / (β - α) = -(1 / (β - α)) by ring, abs_neg,
    abs_of_pos (show 0 < 1 / (β - α) by positivity)]
  calc _ ≤ B * (1 / (β - α)) := mul_le_mul_of_nonneg_right (hB _) (by positivity)
    _ = _ := by ring

end PDE.Parabolic.WeakHarnack
