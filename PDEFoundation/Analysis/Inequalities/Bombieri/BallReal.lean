module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The real-variable estimate in the proof of the Bombieri lemma (Step 2)
-/

@[expose] public section

namespace PDE.Bombieri

/-- Step 2 of the proof of the Bombieri lemma, in real variables. -/
theorem ball_constant_bound (d : ℕ) (ω A q k p r s : ℝ) (hω : 0 < ω) (hA : 0 < A) (hq : 0 < q)
    (hk : 0 < k) (hp : 0 < p) (hpq : p ≤ q / 2) (hr : 1 / 2 ≤ r) (hrs : r < s) (hs : s ≤ 1) :
    ω⁻¹ ^ (1 / q) * (A / ((s - r) ^ k * s ^ d)) ^ (1 / p) ≤
      (max 1 ω⁻¹ * max 1 ((2 ^ d * A) ^ 2) * (s - r) ^ (-(2 * k))) ^ (1 / p - 1 / q) := by
  have hd0 : 0 < s - r := by linarith
  have hd1 : s - r ≤ 1 := by linarith
  set δ := s - r with hδ
  have hs0 : 0 < s := by linarith
  set e := 1 / p - 1 / q with he
  have h1 : 1 / q ≤ e := by
    rw [he]
    have : 2 / q ≤ 1 / p := by
      rw [div_le_div_iff₀ hq hp]; linarith
    have h2 : 2 / q = 1 / q + 1 / q := by ring
    linarith
  have h2 : 1 / (2 * p) ≤ e := by
    have : 1 / q ≤ 1 / (2 * p) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have h3 : 1 / (2 * p) = 1 / p - 1 / (2 * p) := by field_simp; ring
    rw [he]; linarith
  have he0 : 0 ≤ e := le_trans (by positivity) h1
  have hmaxω : 1 ≤ max 1 ω⁻¹ := le_max_left _ _
  set M := max 1 ((2 ^ d * A) ^ 2) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hDneg : 1 ≤ δ ^ (-(2 * k)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1 (by linarith)
  -- first factor
  have ha : ω⁻¹ ^ (1 / q) ≤ (max 1 ω⁻¹) ^ e :=
    calc ω⁻¹ ^ (1 / q) ≤ (max 1 ω⁻¹) ^ (1 / q) :=
          Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by positivity)
      _ ≤ (max 1 ω⁻¹) ^ e := Real.rpow_le_rpow_of_exponent_le hmaxω h1
  -- second factor
  set Y := A / (δ ^ k * s ^ d) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hsd : (1 / 2 : ℝ) ^ d ≤ s ^ d := pow_le_pow_left₀ (by norm_num) (by linarith) d
  have hY1 : Y ≤ 2 ^ d * A / δ ^ k := by
    rw [hY, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 : ℝ) ≤ 2 ^ d * s ^ d := by
      calc (1 : ℝ) = 2 ^ d * (1 / 2) ^ d := by rw [one_div, inv_pow, mul_inv_cancel₀ (by positivity)]
        _ ≤ 2 ^ d * s ^ d := by gcongr
    have hδk : 0 < δ ^ k := by positivity
    nlinarith [mul_pos hA hδk]
  have hY2 : Y ^ 2 ≤ (2 ^ d * A) ^ 2 * δ ^ (-(2 * k)) := by
    have h3 : Y ^ 2 ≤ (2 ^ d * A / δ ^ k) ^ 2 := pow_le_pow_left₀ hY0 hY1 2
    refine h3.trans (le_of_eq ?_)
    rw [div_pow, Real.rpow_neg hd0.le, div_eq_mul_inv]
    congr 2
    rw [mul_comm, Real.rpow_mul hd0.le]
    exact_mod_cast (Real.rpow_natCast (δ ^ k) 2).symm
  have hY3 : max 1 (Y ^ 2) ≤ M * δ ^ (-(2 * k)) := by
    refine max_le ?_ ?_
    · nlinarith
    · calc Y ^ 2 ≤ (2 ^ d * A) ^ 2 * δ ^ (-(2 * k)) := hY2
        _ ≤ M * δ ^ (-(2 * k)) := by gcongr; exact le_max_right _ _
  have hb : Y ^ (1 / p) ≤ (M * δ ^ (-(2 * k))) ^ e := by
    have h4 : Y ^ (1 / p) = (Y ^ 2) ^ (1 / (2 * p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
      congr 1; push_cast; field_simp
    rw [h4]
    calc (Y ^ 2) ^ (1 / (2 * p)) ≤ (max 1 (Y ^ 2)) ^ (1 / (2 * p)) :=
          Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by positivity)
      _ ≤ (max 1 (Y ^ 2)) ^ e := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) h2
      _ ≤ (M * δ ^ (-(2 * k))) ^ e :=
          Real.rpow_le_rpow (by positivity) hY3 he0
  calc ω⁻¹ ^ (1 / q) * Y ^ (1 / p) ≤ (max 1 ω⁻¹) ^ e * (M * δ ^ (-(2 * k))) ^ e :=
        mul_le_mul ha hb (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.mul_rpow (by positivity) (by positivity), mul_assoc]

end PDE.Bombieri
