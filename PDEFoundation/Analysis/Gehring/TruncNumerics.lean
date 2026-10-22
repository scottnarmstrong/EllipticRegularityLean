module

public import PDEFoundation.Analysis.Gehring.TruncatedMax

/-!
# Numerical facts for the truncated maximal function
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem b_facts (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (h2 : ε * ((d : ℝ) + 1) ≤ 1 / 32) :
    1 / ((d : ℝ) + 1) ≤ 1 - gehringTheta d + ε ∧ 1 - gehringTheta d + ε ≤ gehringTheta d := by
  have hθ1 : 1 - gehringTheta d = 1 / ((d : ℝ) + 1) := by
    unfold gehringTheta; field_simp; ring
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · rw [hθ1]; linarith
  · rw [hθ1]
    unfold gehringTheta
    rw [div_add' _ _ _ hdpos.ne', div_le_div_iff₀ hdpos hdpos]
    nlinarith

theorem K_le_G (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (h2 : ε * ((d : ℝ) + 1) ≤ 1 / 32) :
    2 * 3 ^ d * (1 + ε) * (gehringC d ^ (-(1 - gehringTheta d + ε)) /
      (1 - gehringTheta d + ε)) ≤ gehringG d := by
  obtain ⟨hb1, hb2⟩ := b_facts hd hε h2
  set b := 1 - gehringTheta d + ε with hb
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb1
  have hc2 := gehringC_rpow_neg_le hd hb2
  have hc0 : 0 ≤ gehringC d ^ (-b) := Real.rpow_nonneg (gehringC_pos d).le _
  have hinv : 1 / b ≤ (d : ℝ) + 1 := by
    rw [div_le_iff₀ hb0]
    rw [div_le_iff₀ hdpos] at hb1
    linarith
  have hε1 : ε ≤ 1 := by nlinarith
  have hH : 2 ≤ gehringH d := by
    unfold gehringH
    calc (2 : ℝ) ≤ 9 / 2 := by norm_num
      _ = (9 / 2 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (9 / 2) ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (0 : ℝ) < 3 ^ d := by positivity
  calc 2 * 3 ^ d * (1 + ε) * (gehringC d ^ (-b) / b)
      = 2 * 3 ^ d * (1 + ε) * (gehringC d ^ (-b) * (1 / b)) := by ring
    _ ≤ 2 * 3 ^ d * 2 * (2 * ((d : ℝ) + 1)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (mul_le_mul hc2 hinv (by positivity) (by norm_num)) (by positivity) (by positivity)
    _ = 8 * 3 ^ d * ((d : ℝ) + 1) := by ring
    _ ≤ 4 * ((d : ℝ) + 1) * 3 ^ d * gehringH d := by nlinarith [mul_pos h3 hdpos]
    _ = gehringG d := rfl

end PDE.Gehring
