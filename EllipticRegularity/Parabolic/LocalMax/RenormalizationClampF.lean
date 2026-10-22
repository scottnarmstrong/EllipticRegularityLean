/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.RenormalizationClamp
public import EllipticRegularity.Parabolic.Chain.Calculus

/-! # Calculus and uniform bounds for `F ∘ ψ_M` -/

@[expose] public section

namespace PDE.Parabolic.LocalMax

open Filter Topology

variable {F : ℝ → ℝ}

theorem contDiff_clampF (hF : ContDiff ℝ 2 F) (M : ℝ) : ContDiff ℝ 2 (clampF F M) :=
  hF.comp (contDiff_psiM M)

theorem hasDerivAt_clampF (hF : ContDiff ℝ 2 F) {M : ℝ} (hM : M ≠ 0) (s : ℝ) :
    HasDerivAt (clampF F M) (deriv F (psiM M s) * dpsiM M s) s :=
  (((hF.differentiable (by norm_num)) _).hasDerivAt).comp s (hasDerivAt_psiM hM s)

theorem deriv_clampF (hF : ContDiff ℝ 2 F) {M : ℝ} (hM : M ≠ 0) :
    deriv (clampF F M) = fun s => deriv F (psiM M s) * dpsiM M s :=
  funext fun s => (hasDerivAt_clampF hF hM s).deriv

theorem deriv_deriv_clampF (hF : ContDiff ℝ 2 F) {M : ℝ} (hM : M ≠ 0) (s : ℝ) :
    deriv (deriv (clampF F M)) s =
      deriv (deriv F) (psiM M s) * dpsiM M s * dpsiM M s +
        deriv F (psiM M s) * ddpsiM M s := by
  rw [deriv_clampF hF hM]
  have h1 : HasDerivAt (deriv F) (deriv (deriv F) (psiM M s)) (psiM M s) :=
    (((Chain.contDiff_deriv_of_two hF).differentiable (by norm_num)) _).hasDerivAt
  have hA := h1.comp s (hasDerivAt_psiM hM s)
  exact (hA.mul (hasDerivAt_dpsiM s)).deriv

section bounds

variable {C : ℝ}

theorem abs_deriv_le (hC : ∀ s, |deriv (deriv F) s| ≤ C) (hF : ContDiff ℝ 2 F) (r : ℝ) :
    |deriv F r| ≤ |deriv F 0| + C * |r| := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (deriv F) x := fun x _ =>
    ((Chain.contDiff_deriv_of_two hF).differentiable (by norm_num)) x
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd (fun x _ => hC x) convex_univ
    (Set.mem_univ 0) (Set.mem_univ r)
  simp only [Real.norm_eq_abs, sub_zero] at h
  calc |deriv F r| = |deriv F 0 + (deriv F r - deriv F 0)| := by ring_nf
    _ ≤ |deriv F 0| + |deriv F r - deriv F 0| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_le_quad (hC : ∀ s, |deriv (deriv F) s| ≤ C) (hF : ContDiff ℝ 2 F) (r : ℝ) :
    |F r| ≤ |F 0| + (|deriv F 0| + C * |r|) * |r| := by
  have hd : ∀ x ∈ Metric.closedBall (0 : ℝ) |r|, DifferentiableAt ℝ F x := fun x _ =>
    (hF.differentiable (by norm_num)) x
  have hb : ∀ x ∈ Metric.closedBall (0 : ℝ) |r|, ‖deriv F x‖ ≤ |deriv F 0| + C * |r| := by
    intro x hx
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hx
    have h1 := abs_deriv_le hC hF x
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    rw [Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hx hC0]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_closedBall (0 : ℝ) |r|)
    (Metric.mem_closedBall_self (abs_nonneg r)) (by simp : r ∈ Metric.closedBall (0 : ℝ) |r|)
  simp only [Real.norm_eq_abs, sub_zero] at h
  calc |F r| = |F 0 + (F r - F 0)| := by ring_nf
    _ ≤ |F 0| + |F r - F 0| := abs_add_le _ _
    _ ≤ _ := by linarith

variable (hC : ∀ s, |deriv (deriv F) s| ≤ C) (hF : ContDiff ℝ 2 F)
include hC hF

theorem abs_clampF_le {M : ℝ} (hM : 0 < M) (s : ℝ) :
    |clampF F M s| ≤ |F 0| + |deriv F 0| * |s| + C * s ^ 2 := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := abs_le_quad hC hF (psiM M s)
  have h2 := abs_psiM_le M s hM
  have h3 : 0 ≤ |psiM M s| := abs_nonneg _
  have h4 : (|deriv F 0| + C * |psiM M s|) * |psiM M s| ≤ (|deriv F 0| + C * |s|) * |s| :=
    mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left h2 hC0]) h2 h3
      (by positivity)
  have h5 : |s| ^ 2 = s ^ 2 := sq_abs s
  unfold clampF
  nlinarith [h5]

theorem abs_deriv_clampF_le {M : ℝ} (hM : 0 < M) (s : ℝ) :
    |deriv F (psiM M s) * dpsiM M s| ≤ |deriv F 0| + C * |s| := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := abs_deriv_le hC hF (psiM M s)
  have h2 := abs_psiM_le M s hM
  have h3 := dpsiM_pos M s
  have h4 := dpsiM_le_one M s
  rw [abs_mul, abs_of_pos h3]
  have h5 : |deriv F 0| + C * |psiM M s| ≤ |deriv F 0| + C * |s| := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hC0]
  calc |deriv F (psiM M s)| * dpsiM M s ≤ (|deriv F 0| + C * |s|) * dpsiM M s :=
        mul_le_mul_of_nonneg_right (h1.trans h5) h3.le
    _ ≤ (|deriv F 0| + C * |s|) * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

theorem abs_deriv_clampF_le_const {M : ℝ} (hM : 0 < M) (s : ℝ) :
    |deriv F (psiM M s) * dpsiM M s| ≤ |deriv F 0| + C * M / 2 := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := abs_deriv_le hC hF (psiM M s)
  have h3 := dpsiM_pos M s
  have h4 := dpsiM_le_one M s
  have h6 := abs_psiM_mul_dpsiM_le M s hM
  rw [abs_mul, abs_of_pos h3]
  calc |deriv F (psiM M s)| * dpsiM M s
      ≤ (|deriv F 0| + C * |psiM M s|) * dpsiM M s :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = |deriv F 0| * dpsiM M s + C * (|psiM M s| * dpsiM M s) := by ring
    _ ≤ |deriv F 0| * 1 + C * (M / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left h4 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h6 hC0)
    _ = _ := by ring

theorem abs_deriv_deriv_clampF_le {M : ℝ} (hM : 1 ≤ M) (s : ℝ) :
    |deriv (deriv F) (psiM M s) * dpsiM M s * dpsiM M s +
      deriv F (psiM M s) * ddpsiM M s| ≤ 3 * C + |deriv F 0| := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := abs_deriv_le hC hF (psiM M s)
  have h3 := dpsiM_pos M s
  have h4 := dpsiM_le_one M s
  have h7 := abs_ddpsiM_le M s hM0
  have h8 := abs_psiM_mul_ddpsiM_le M s hM0
  have h9 : 1 / M ≤ 1 := by rw [div_le_one hM0]; exact hM
  have h7' : |ddpsiM M s| ≤ 1 := h7.trans h9
  have hA : |deriv (deriv F) (psiM M s) * dpsiM M s * dpsiM M s| ≤ C := by
    rw [abs_mul, abs_mul, abs_of_pos h3]
    have h10 : dpsiM M s * dpsiM M s ≤ 1 := by nlinarith
    calc |deriv (deriv F) (psiM M s)| * dpsiM M s * dpsiM M s
        = |deriv (deriv F) (psiM M s)| * (dpsiM M s * dpsiM M s) := by ring
      _ ≤ C * 1 := mul_le_mul (hC _) h10 (by positivity) hC0
      _ = C := by ring
  have hB : |deriv F (psiM M s) * ddpsiM M s| ≤ 2 * C + |deriv F 0| := by
    rw [abs_mul]
    calc |deriv F (psiM M s)| * |ddpsiM M s|
        ≤ (|deriv F 0| + C * |psiM M s|) * |ddpsiM M s| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |deriv F 0| * |ddpsiM M s| + C * (|psiM M s| * |ddpsiM M s|) := by ring
      _ ≤ |deriv F 0| * 1 + C * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h7' (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h8 hC0)
      _ = _ := by ring
  calc _ ≤ |deriv (deriv F) (psiM M s) * dpsiM M s * dpsiM M s| +
        |deriv F (psiM M s) * ddpsiM M s| := abs_add_le _ _
    _ ≤ _ := by linarith

end bounds

end PDE.Parabolic.LocalMax
