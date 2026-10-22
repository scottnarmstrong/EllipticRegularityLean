module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Dyadic radii and scale weights -/

@[expose] public section

namespace PDE

/-- A dyadic radius, in the same convention as the centered-cube API. -/
noncomputable def dyadicRadius (R : ℝ) (n : ℕ) : ℝ := R / (2 : ℝ) ^ n

@[simp] theorem dyadicRadius_zero (R : ℝ) : dyadicRadius R 0 = R := by
  simp [dyadicRadius]

theorem dyadicRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < dyadicRadius R n := by unfold dyadicRadius; positivity

theorem dyadicRadius_succ (R : ℝ) (n : ℕ) :
    dyadicRadius R (n + 1) = dyadicRadius R n / 2 := by
  simp only [dyadicRadius, pow_succ, div_mul_eq_div_div]

theorem dyadicRadius_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    dyadicRadius R n ≤ R := by
  exact div_le_self hR (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ n)

theorem dyadicRadius_succ_rpow {R : ℝ} (hR : 0 ≤ R) (β : ℝ) (n : ℕ) :
    dyadicRadius R (n + 1) ^ β =
      (1 / 2 : ℝ) ^ β * dyadicRadius R n ^ β := by
  rw [dyadicRadius_succ, show dyadicRadius R n / 2 =
    (1 / 2 : ℝ) * dyadicRadius R n by ring]
  exact Real.mul_rpow (by norm_num) (div_nonneg hR (by positivity))

/-- Every smaller positive radius lies between two consecutive dyadic radii. -/
theorem exists_dyadicRadius_bracket {R s : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R) :
    ∃ n : ℕ, dyadicRadius R (n + 1) < s ∧ s ≤ dyadicRadius R n := by
  obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hs hR) ((div_le_one hR).2 hsR)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have heq (k : ℕ) : dyadicRadius R k = R * (1 / 2 : ℝ) ^ k := by
    simp only [dyadicRadius, one_div, inv_pow]
    rfl
  refine ⟨n, ?_, ?_⟩
  · rw [heq]
    simpa only [mul_comm] using (lt_div_iff₀ hR).1 hnlow
  · rw [heq]
    simpa only [mul_comm] using (div_le_iff₀ hR).1 hnhigh

end PDE
