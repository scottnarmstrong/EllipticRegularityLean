module

public import PDEFoundation.Analysis.Gehring.LocalItLimit

/-!
# Constants and normalized norms for the local Gehring estimate
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The explicit constant of the local Gehring estimate: `2^{d+4} N_4`. -/
noncomputable def gehringLocalC (d : ℕ) : ℝ := 2 ^ (d + 4) * gehringN 4 d

theorem gehringN_four_pos (d : ℕ) : 0 < gehringN 4 d := gehringN_pos 4 (Or.inr rfl) d

theorem one_le_gehringN_four (d : ℕ) : 1 ≤ gehringN 4 d := by
  unfold gehringN
  have : (1 : ℝ) ≤ (4 + 1) ^ d := one_le_pow₀ (by norm_num)
  linarith

theorem one_le_gehringLocalC (d : ℕ) : 1 ≤ gehringLocalC d := by
  unfold gehringLocalC
  have h1 : (1 : ℝ) ≤ 2 ^ (d + 4) := one_le_pow₀ (by norm_num)
  have h2 := one_le_gehringN_four d
  nlinarith

/-- The normalized `L^p` norm of a nonnegative function as a normalized lintegral. -/
theorem eLpMeanNormOn_eq_lintegral {U : Set (Vec d)} (hU : volume U < ⊤) {f : Vec d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f (volumeOn U)) {p : ℝ} (hp : 0 < p) :
    eLpMeanNormOn U (ENNReal.ofReal p) f =
      ((volume U)⁻¹ * ∫⁻ x in U, ENNReal.ofReal (f x) ^ p) ^ (1 / p) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hU, eLpNormOn,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal hp.le]
  have hq : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div]
  rw [hq, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 2
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x)]

theorem real_X_le {m : ℝ} (hm : 0 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    (2 ^ (d + 2) * m ^ (1 + ε)) ^ (1 / (1 + ε)) ≤ 2 ^ (d + 2) * m := by
  have hp : 0 < 1 + ε := by linarith
  have hq1 : 1 / (1 + ε) ≤ 1 := by rw [div_le_one hp]; linarith
  have h2 : (1 : ℝ) ≤ 2 ^ (d + 2) := one_le_pow₀ (by norm_num)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hm,
    mul_one_div_cancel hp.ne', Real.rpow_one]
  refine mul_le_mul_of_nonneg_right ?_ hm
  calc ((2 : ℝ) ^ (d + 2)) ^ (1 / (1 + ε)) ≤ ((2 : ℝ) ^ (d + 2)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h2 hq1
    _ = 2 ^ (d + 2) := Real.rpow_one _

theorem real_Y_le (hd : 2 ≤ d) {σ B ε : ℝ} (hσ : σ = 2 ∨ σ = 4) (hB : 0 ≤ B) (hε : 0 < ε)
    (hεG : ε ≤ 1 / (8 * gehringG d)) :
    (2 ^ d * (4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)))) ^ (1 / (1 + ε)) ≤
      gehringLocalC d * B := by
  have hp : 0 < 1 + ε := by linarith
  have hq1 : 1 / (1 + ε) ≤ 1 := by rw [div_le_one hp]; linarith
  have hN := gehringN_pos σ hσ d
  have hNN := gehringN_le σ hσ d
  have hG4 := four_mul_succ_le_gehringG d
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hG := gehringG_pos d
  have hε64 : ε / (1 + ε) ≤ 1 / (8 * 8) := by
    have h1 : ε / (1 + ε) ≤ ε := div_le_self hε.le (by linarith)
    refine h1.trans (hεG.trans ?_)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE1 : (1 : ℝ) ≤ 2 ^ d * (4 / 3) := by
    have : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  have hE2 : (2 : ℝ) ^ d * (4 / 3) ≤ 2 ^ (d + 1) := by
    rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) d]
  have h1 : (2 ^ d * (4 / 3) : ℝ) ^ (1 / (1 + ε)) ≤ 2 ^ (d + 1) :=
    calc (2 ^ d * (4 / 3) : ℝ) ^ (1 / (1 + ε)) ≤ (2 ^ d * (4 / 3) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hE1 hq1
      _ = 2 ^ d * (4 / 3) := Real.rpow_one _
      _ ≤ _ := hE2
  have h2 : ((8 : ℝ) ^ ε) ^ (1 / (1 + ε)) ≤ 2 := by
    rw [← Real.rpow_mul (by norm_num)]
    have := rpow_le_two (X := 8) (by norm_num) (e := ε * (1 / (1 + ε))) (by positivity)
      (by rw [mul_one_div]; exact hε64)
    exact this
  have h3 : ((2 * B * gehringN σ d) ^ (1 + ε)) ^ (1 / (1 + ε)) = 2 * B * gehringN σ d := by
    rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp.ne', Real.rpow_one]
  have hA0 : (0 : ℝ) ≤ 2 ^ d * (4 / 3) := by positivity
  have hb0 : (0 : ℝ) ≤ 8 ^ ε := by positivity
  have hc0 : (0 : ℝ) ≤ (2 * B * gehringN σ d) ^ (1 + ε) := by positivity
  rw [show (2 : ℝ) ^ d * (4 / 3 * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε))) =
      (2 ^ d * (4 / 3)) * (8 ^ ε * (2 * B * gehringN σ d) ^ (1 + ε)) by ring,
    Real.mul_rpow hA0 (mul_nonneg hb0 hc0), Real.mul_rpow hb0 hc0, h3]
  have hgoal : 2 ^ (d + 1) * (2 * (2 * B * gehringN σ d)) ≤ gehringLocalC d * B := by
    unfold gehringLocalC
    have h4 : (2 : ℝ) ^ (d + 4) = 2 ^ (d + 1) * 8 := by rw [pow_add, pow_add]; ring
    rw [h4]
    have : gehringN σ d * B ≤ gehringN 4 d * B := mul_le_mul_of_nonneg_right hNN hB
    have h5 : 0 < (2 : ℝ) ^ (d + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h5.le, mul_nonneg hN.le hB]
  calc (2 ^ d * (4 / 3) : ℝ) ^ (1 / (1 + ε)) * (((8 : ℝ) ^ ε) ^ (1 / (1 + ε)) *
        (2 * B * gehringN σ d)) ≤ 2 ^ (d + 1) * (2 * (2 * B * gehringN σ d)) := by
        gcongr
    _ ≤ _ := hgoal

end PDE.Gehring
