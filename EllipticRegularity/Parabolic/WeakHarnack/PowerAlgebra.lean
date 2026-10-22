/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import PDEFoundation.Ambient.EuclideanNorm

/-! # Algebra of the power step: constants and `ℝ≥0∞` exponent bookkeeping -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

/-- The constants of the energy estimate are bounded by `K (X + T)` with `K` depending on
`M0 ≥ |r|/(1-r)` and `Λ` only. -/
theorem const_bound {r Λ X T M0 : ℝ} (hr0 : r ≠ 0) (hr1 : r < 1) (hΛ : 0 ≤ Λ) (hX : 0 ≤ X)
    (hT : 0 ≤ T) (hm : |r| / (1 - r) ≤ M0) :
    (2 * T + 2 * |r| * Λ * X / (1 - r)) ≤ (2 + 2 * M0 * Λ) * (X + T) ∧
      r ^ 2 / 2 * ((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) + 2 * X ≤
        (M0 * (2 + 2 * M0 * Λ) + 2) * (X + T) := by
  have h1 : 0 < 1 - r := by linarith
  have habs : 0 < |r| := abs_pos.2 hr0
  set m := |r| / (1 - r) with hmdef
  have hm0 : 0 ≤ m := by positivity
  have e1 : 2 * |r| * Λ * X / (1 - r) = 2 * m * Λ * X := by
    rw [hmdef]; field_simp
  have hS : 2 * T + 2 * |r| * Λ * X / (1 - r) = 2 * T + 2 * m * Λ * X := by rw [e1]
  have e2 : r ^ 2 / 2 * ((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) =
      m * (2 * T + 2 * m * Λ * X) := by
    rw [hmdef]
    have : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    rw [this]; field_simp
  have hMm : 0 ≤ M0 := hm0.trans hm
  have hΛX : 0 ≤ Λ * X := mul_nonneg hΛ hX
  have hA : 2 * T + 2 * m * Λ * X ≤ (2 + 2 * M0 * Λ) * (X + T) := by
    have : m * Λ * X ≤ M0 * Λ * X := by
      have := mul_le_mul_of_nonneg_right hm hΛX
      linarith [this]
    have h3 : M0 * Λ * X ≤ M0 * Λ * (X + T) := by
      have := mul_nonneg (mul_nonneg hMm hΛ) hT
      nlinarith
    nlinarith
  refine ⟨by rw [hS]; exact hA, ?_⟩
  rw [e2]
  have h4 : m * (2 * T + 2 * m * Λ * X) ≤ M0 * ((2 + 2 * M0 * Λ) * (X + T)) :=
    mul_le_mul hm hA (by positivity) hMm
  nlinarith

/-- `L ≤ C M^(2/d) M` gives `L^(1/χ) ≤ C^(1/χ) M` for `χ = (d+2)/d`. -/
theorem lintegral_pow_step {d : ℕ} (hd : 0 < d) {C L M : ℝ≥0∞} (hC : C ≠ ∞)
    (hL : L ≤ C * M ^ (2 / (d : ℝ)) * M) :
    L ^ (1 / (((d : ℝ) + 2) / d)) ≤ C ^ (1 / (((d : ℝ) + 2) / d)) * M := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set χ : ℝ := ((d : ℝ) + 2) / d with hχ
  have hχ1 : χ = 2 / (d : ℝ) + 1 := by rw [hχ]; field_simp; ring
  have hχ0 : 0 < χ := by rw [hχ]; positivity
  have hinv : 0 ≤ 1 / χ := by positivity
  by_cases hM0 : M = 0
  · subst hM0
    have : L = 0 := by
      simpa [ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 2 / d by positivity)] using hL
    rw [this, ENNReal.zero_rpow_of_pos (by positivity)]; simp
  by_cases hMt : M = ⊤
  · subst hMt
    by_cases hC0 : C = 0
    · have hL0 : L = 0 := by simpa [hC0] using hL
      rw [hL0, ENNReal.zero_rpow_of_pos (by positivity)]; exact bot_le
    · have hne : C ^ (1 / χ) ≠ 0 := by
        intro h
        rw [ENNReal.rpow_eq_zero_iff] at h
        rcases h with h | h
        · exact hC0 h.1
        · exact hC h.1
      rw [ENNReal.mul_top hne]
      exact le_top
  have hM : M ^ (2 / (d : ℝ)) * M = M ^ χ := by
    rw [hχ1, ENNReal.rpow_add _ _ hM0 hMt, ENNReal.rpow_one]
  have : L ≤ C * M ^ χ := by rw [mul_assoc, hM] at hL; exact hL
  calc L ^ (1 / χ) ≤ (C * M ^ χ) ^ (1 / χ) := ENNReal.rpow_le_rpow this hinv
    _ = C ^ (1 / χ) * M := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ← ENNReal.rpow_mul]
      rw [mul_one_div_cancel hχ0.ne', ENNReal.rpow_one]

end PDE.Parabolic.WeakHarnack
