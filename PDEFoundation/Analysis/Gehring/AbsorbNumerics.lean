module

public import PDEFoundation.Analysis.Gehring.AbsorbCore
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical facts for the absorption
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem gehringD_pos (d : ℕ) : 0 < gehringD d := by
  unfold gehringD; have := gehringH_pos d; positivity

theorem gehringG_eq (d : ℕ) : gehringG d = 2 * ((d : ℝ) + 1) * gehringD d := by
  unfold gehringG gehringD; ring

theorem gehringG_pos (d : ℕ) : 0 < gehringG d := by
  unfold gehringG; have := gehringH_pos d; positivity

theorem four_mul_succ_le_gehringG (d : ℕ) : 4 * ((d : ℝ) + 1) ≤ gehringG d := by
  unfold gehringG
  have h1 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h2 := one_le_gehringH d
  have h3 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg h3 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h3 (by positivity : (0:ℝ) ≤ 3 ^ d))
    (sub_nonneg.2 h2)]

/-- `ε ≤ 1/(8 G A)` with `A ≥ 1` gives `ε (d+1) ≤ 1/32` and `ε A G ≤ 1/8`. -/
theorem eps_bounds {d : ℕ} {A ε : ℝ} (hA : 1 ≤ A) (hε : 0 < ε)
    (h : ε ≤ 1 / (8 * gehringG d * A)) :
    ε * A * gehringG d ≤ 1 / 8 ∧ ε * ((d : ℝ) + 1) ≤ 1 / 32 := by
  have hG := gehringG_pos d
  have hG4 := four_mul_succ_le_gehringG d
  have hA0 : 0 < A := by linarith
  have h1 : ε * (8 * gehringG d * A) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at h
  constructor
  · nlinarith
  · have : ε * (8 * (4 * ((d : ℝ) + 1)) * 1) ≤ ε * (8 * gehringG d * A) := by
      refine mul_le_mul_of_nonneg_left ?_ hε.le
      have : 4 * ((d : ℝ) + 1) * 1 ≤ gehringG d * A := mul_le_mul hG4 hA (by norm_num) hG.le
      nlinarith
    nlinarith

theorem gehringC_rpow_neg_le (hd : 2 ≤ d) {b : ℝ} (hb2 : b ≤ gehringTheta d) :
    gehringC d ^ (-b) ≤ 2 := by
  have hd0 : 0 < d := by omega
  have hθ := gehringTheta_pos hd0
  unfold gehringC
  rw [← Real.rpow_mul (by norm_num)]
  calc (2 : ℝ) ^ (-(1 / gehringTheta d) * -b) ≤ 2 ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [neg_mul_neg, one_div_mul_eq_div, div_le_one hθ]
        exact hb2
    _ = 2 := Real.rpow_one 2

/-- `X ≥ 1` and `0 ≤ e ≤ 1/(8X)` give `X^e ≤ 2`. -/
theorem rpow_le_two {X e : ℝ} (hX : 1 ≤ X) (he0 : 0 ≤ e) (he : e ≤ 1 / (8 * X)) : X ^ e ≤ 2 := by
  have hX0 : 0 < X := by linarith
  have hlog : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hX0
  have h1 : Real.log X * e ≤ 1 / 8 := by
    have h2 : Real.log X * e ≤ (X - 1) * e := mul_le_mul_of_nonneg_right hlog he0
    have h3 : (X - 1) * e ≤ (X - 1) * (1 / (8 * X)) :=
      mul_le_mul_of_nonneg_left he (by linarith)
    have h4 : (X - 1) * (1 / (8 * X)) ≤ 1 / 8 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hl : (1 : ℝ) / 8 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  rw [Real.rpow_def_of_pos hX0]
  calc Real.exp (Real.log X * e) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.2 (h1.trans hl)
    _ = 2 := Real.exp_log (by norm_num)

/-- The absorption coefficient `β = ε D A c^{-b} / b` is at most `1/8`. -/
theorem beta_le (hd : 2 ≤ d) {A ε : ℝ} (hA : 1 ≤ A) (hε : 0 < ε)
    (h : ε ≤ 1 / (8 * gehringG d * A)) :
    ε * gehringD d * A * (gehringC d ^ (-(1 - gehringTheta d + ε)) /
      (1 - gehringTheta d + ε)) ≤ 1 / 8 := by
  have hd0 : 0 < d := by omega
  obtain ⟨h1, h2⟩ := eps_bounds hA hε h
  have hθ1 : 1 - gehringTheta d = 1 / ((d : ℝ) + 1) := by
    unfold gehringTheta; field_simp; ring
  set b := 1 - gehringTheta d + ε with hb
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have hbpos : 1 / ((d : ℝ) + 1) ≤ b := by rw [hb, hθ1]; linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hbpos
  have hε1 : ε ≤ 1 / ((d : ℝ) + 1) := by
    rw [le_div_iff₀ hdpos]; linarith
  have hbθ : b ≤ gehringTheta d := by
    rw [hb, hθ1]
    unfold gehringTheta
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_add' _ _ _ hdpos.ne', div_le_div_iff₀ hdpos hdpos]
    nlinarith
  have hc2 := gehringC_rpow_neg_le hd hbθ
  have hc0 : 0 ≤ gehringC d ^ (-b) := Real.rpow_nonneg (gehringC_pos d).le _
  have hD := gehringD_pos d
  have hinv : 1 / b ≤ (d : ℝ) + 1 := by
    rw [div_le_iff₀ hb0]
    rw [div_le_iff₀ hdpos] at hbpos
    linarith
  calc ε * gehringD d * A * (gehringC d ^ (-b) / b)
      = ε * gehringD d * A * (gehringC d ^ (-b) * (1 / b)) := by ring
    _ ≤ ε * gehringD d * A * (2 * ((d : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hc2 hinv (by positivity) (by norm_num)
    _ = ε * A * gehringG d := by rw [gehringG_eq]; ring
    _ ≤ 1 / 8 := h1

end PDE.Gehring
