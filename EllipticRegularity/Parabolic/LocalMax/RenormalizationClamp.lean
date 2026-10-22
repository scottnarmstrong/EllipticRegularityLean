/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.MeanValue

/-! # An arctan clamp for renormalization

For `M ≥ 1` the function `ψ_M s = M * arctan (s / M)` is smooth, satisfies `|ψ_M s| ≤ |s|`,
and has bounded first and second derivatives. Composing a `C²` function `F` with a
bounded second derivative with `ψ_M` produces a `C²` function with bounded first and second
derivatives, with bounds uniform in `M` for the quantities that matter in the limit `M → ∞`.
-/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open Filter Topology

/-- The clamp `ψ_M s = M * arctan (s / M)`. -/
noncomputable def psiM (M s : ℝ) : ℝ := M * Real.arctan (s / M)

/-- First derivative of the clamp. -/
noncomputable def dpsiM (M s : ℝ) : ℝ := 1 / (1 + (s / M) ^ 2)

/-- Second derivative of the clamp. -/
noncomputable def ddpsiM (M s : ℝ) : ℝ := -(2 * (s / M) / M) / (1 + (s / M) ^ 2) ^ 2

/-- The composed function `F ∘ ψ_M`. -/
noncomputable def clampF (F : ℝ → ℝ) (M : ℝ) : ℝ → ℝ := fun s => F (psiM M s)

theorem contDiff_psiM (M : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (psiM M) :=
  contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const M))

theorem hasDerivAt_psiM {M : ℝ} (hM : M ≠ 0) (s : ℝ) :
    HasDerivAt (psiM M) (dpsiM M s) s := by
  have h1 : HasDerivAt (fun s : ℝ => s / M) (1 / M) s := by
    simpa using (hasDerivAt_id s).div_const M
  have h2 := (h1.arctan).const_mul M
  unfold dpsiM
  refine h2.congr_deriv ?_
  field_simp

theorem hasDerivAt_dpsiM {M : ℝ} (s : ℝ) :
    HasDerivAt (dpsiM M) (ddpsiM M s) s := by
  have h1 : HasDerivAt (fun s : ℝ => s / M) (1 / M) s := by
    simpa using (hasDerivAt_id s).div_const M
  have h2 : HasDerivAt (fun s : ℝ => 1 + (s / M) ^ 2) (2 * (s / M) * (1 / M)) s := by
    simpa using (h1.pow 2).const_add 1
  have hne : (1 + (s / M) ^ 2) ≠ 0 := by positivity
  have h3 : HasDerivAt (fun s : ℝ => 1 / (1 + (s / M) ^ 2))
      ((0 * (1 + (s / M) ^ 2) - 1 * (2 * (s / M) * (1 / M))) / (1 + (s / M) ^ 2) ^ 2) s :=
    (hasDerivAt_const s (1 : ℝ)).div h2 hne
  unfold ddpsiM dpsiM
  refine h3.congr_deriv ?_
  ring

theorem dpsiM_pos (M s : ℝ) : 0 < dpsiM M s := by
  unfold dpsiM; positivity

theorem dpsiM_le_one (M s : ℝ) : dpsiM M s ≤ 1 := by
  unfold dpsiM
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (s / M)]

theorem abs_psiM_le (M s : ℝ) (hM : 0 < M) : |psiM M s| ≤ |s| := by
  unfold psiM
  rw [abs_mul, abs_of_pos hM]
  calc M * |Real.arctan (s / M)| ≤ M * |s / M| :=
        mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs hM.le
    _ = |s| := by rw [abs_div, abs_of_pos hM]; field_simp

theorem two_abs_le_one_add_sq (x : ℝ) : 2 * |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_abs x, sq_nonneg (|x| - 1)]

theorem abs_psiM_mul_dpsiM_le (M s : ℝ) (hM : 0 < M) :
    |psiM M s| * dpsiM M s ≤ M / 2 := by
  have hx := two_abs_le_one_add_sq (s / M)
  have h1 : |psiM M s| ≤ M * |s / M| := by
    unfold psiM
    rw [abs_mul, abs_of_pos hM]
    exact mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs hM.le
  unfold dpsiM at *
  have hd : 0 < 1 + (s / M) ^ 2 := by positivity
  calc |psiM M s| * (1 / (1 + (s / M) ^ 2)) ≤ (M * |s / M|) * (1 / (1 + (s / M) ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = M * (|s / M| / (1 + (s / M) ^ 2)) := by ring
    _ ≤ M * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ hM.le
        rw [div_le_iff₀ hd]
        linarith
    _ = M / 2 := by ring

theorem abs_ddpsiM_le (M s : ℝ) (hM : 0 < M) : |ddpsiM M s| ≤ 1 / M := by
  have hx := two_abs_le_one_add_sq (s / M)
  have hd : 1 ≤ 1 + (s / M) ^ 2 := by nlinarith [sq_nonneg (s / M)]
  have hd2 : 1 + (s / M) ^ 2 ≤ (1 + (s / M) ^ 2) ^ 2 := by nlinarith
  unfold ddpsiM
  rw [abs_div, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + (s / M) ^ 2) ^ 2),
    abs_mul, abs_of_pos hM, abs_two]
  rw [div_div, div_le_div_iff₀ (by positivity) hM]
  have : 2 * |s / M| ≤ (1 + (s / M) ^ 2) ^ 2 := hx.trans hd2
  calc 2 * |s / M| * M ≤ (1 + (s / M) ^ 2) ^ 2 * M :=
        mul_le_mul_of_nonneg_right this hM.le
    _ = _ := by ring

theorem abs_psiM_mul_ddpsiM_le (M s : ℝ) (hM : 0 < M) :
    |psiM M s| * |ddpsiM M s| ≤ 2 := by
  have h1 : |psiM M s| ≤ M * |s / M| := by
    unfold psiM
    rw [abs_mul, abs_of_pos hM]
    exact mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs hM.le
  set x := s / M with hx
  have hd : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hd2 : 0 < (1 + x ^ 2) ^ 2 := by positivity
  have h2 : |ddpsiM M s| = 2 * |x| / M / (1 + x ^ 2) ^ 2 := by
    unfold ddpsiM
    rw [← hx, abs_div, abs_neg, abs_of_pos hd2, abs_div, abs_mul, abs_of_pos hM, abs_two]
  rw [h2]
  have h3 : |psiM M s| * (2 * |x| / M / (1 + x ^ 2) ^ 2) ≤
      (M * |x|) * (2 * |x| / M / (1 + x ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h4 : (M * |x|) * (2 * |x| / M / (1 + x ^ 2) ^ 2) = 2 * x ^ 2 / (1 + x ^ 2) ^ 2 := by
    have := sq_abs x
    field_simp
    rw [this]
  have h5 : 2 * x ^ 2 / (1 + x ^ 2) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ hd2]
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  linarith

end PDE.Parabolic.LocalMax
