module

public import PDEFoundation.Regularity.DyadicCampanato
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Dependence of the dyadic Campanato constant on the exponent

This module makes the `1 / α` dependence of the existing dyadic
Campanato-to-Hölder constant explicit.
-/

@[expose] public section

namespace PDE

private theorem two_rpow_lower_linear {α : ℝ} (hα0 : 0 < α) :
    1 + α / 2 ≤ (2 : ℝ) ^ α := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hlog' :=
      Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  have harg : α / 2 ≤ Real.log 2 * α := by
    calc
      α / 2 = α * (1 / 2) := by ring
      _ ≤ α * Real.log 2 := mul_le_mul_of_nonneg_left hlog hα0.le
      _ = Real.log 2 * α := by ring
  have hexp_tangent : Real.log 2 * α + 1 ≤ Real.exp (Real.log 2 * α) :=
    Real.add_one_le_exp _
  calc
    1 + α / 2 ≤ Real.log 2 * α + 1 := by linarith only [harg]
    _ ≤ Real.exp (Real.log 2 * α) := hexp_tangent
    _ = (2 : ℝ) ^ α := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The denominator in the exact dyadic geometric tail is at least `α / 4`
for exponents in `(0, 1)`. -/
theorem one_sub_two_rpow_neg_ge_div_four {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    α / 4 ≤ 1 - (2 : ℝ) ^ (-α) := by
  let P : ℝ := (2 : ℝ) ^ α
  have hPpos : 0 < P := by
    dsimp [P]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α
  have hPlower : 1 + α / 2 ≤ P := by
    dsimp [P]
    exact two_rpow_lower_linear hα0
  have hPupper : P ≤ 2 := by
    dsimp [P]
    calc
      (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
      _ = 2 := by norm_num
  have hproduct : α / 4 * P ≤ α / 2 := by
    calc
      α / 4 * P ≤ α / 4 * 2 :=
        mul_le_mul_of_nonneg_left hPupper (by positivity)
      _ = α / 2 := by ring
  have hnumerator : α / 4 * P ≤ P - 1 := by
    calc
      α / 4 * P ≤ α / 2 := hproduct
      _ ≤ P - 1 := by linarith only [hPlower]
  have hratio : α / 4 ≤ (P - 1) / P :=
    (le_div_iff₀ hPpos).2 hnumerator
  have hrewrite : 1 - P⁻¹ = (P - 1) / P := by
    field_simp [ne_of_gt hPpos]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change α / 4 ≤ 1 - P⁻¹
  rw [hrewrite]
  exact hratio

/-- The explicit dyadic Campanato-to-Hölder constant has at most the stated
dimension dependence and `1 / α` growth for `0 < α < 1`. -/
theorem dyadicCampanatoHolderConst_le_inv_alpha
    (d : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    dyadicCampanatoHolderConst d α ≤
      (32 * Real.sqrt ((2 : ℝ) ^ d)) / α := by
  let S : ℝ := Real.sqrt ((2 : ℝ) ^ d)
  let P : ℝ := (2 : ℝ) ^ α
  let T : ℝ := dyadicCampanatoTailConst d α
  let C : ℝ := S / α
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := div_nonneg hS hα0.le
  have hPpos : 0 < P := by
    dsimp [P]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α
  have hPupper : P ≤ 2 := by
    dsimp [P]
    calc
      (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
      _ = 2 := by norm_num
  have hden : α / 4 ≤ 1 - (2 : ℝ) ^ (-α) :=
    one_sub_two_rpow_neg_ge_div_four hα0 hα1
  have htail : T ≤ 4 * C := by
    dsimp [T, dyadicCampanatoTailConst]
    calc
      S / (1 - (2 : ℝ) ^ (-α)) ≤ S / (α / 4) :=
        div_le_div_of_nonneg_left hS (by positivity) hden
      _ = 4 * C := by
        dsimp [C]
        field_simp
  have htwoTail : 2 * T ≤ 8 * C := by
    calc
      2 * T ≤ 2 * (4 * C) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = 8 * C := by ring
  have hterm₁ : (2 * T) * P ≤ 16 * C := by
    calc
      (2 * T) * P ≤ (8 * C) * P :=
        mul_le_mul_of_nonneg_right htwoTail hPpos.le
      _ ≤ (8 * C) * 2 :=
        mul_le_mul_of_nonneg_left hPupper (mul_nonneg (by norm_num) hC)
      _ = 16 * C := by ring
  have hPproduct : P * P ≤ 4 := by
    calc
      P * P ≤ 2 * 2 :=
        mul_le_mul hPupper hPupper hPpos.le (by norm_num)
      _ = 4 := by norm_num
  have hSC : S ≤ C := by
    apply (le_div_iff₀ hα0).2
    have hmul : S * α ≤ S * 1 :=
      mul_le_mul_of_nonneg_left hα1.le hS
    simpa using hmul
  have hterm₂ : (2 * S * P) * P ≤ 8 * C := by
    calc
      (2 * S * P) * P = (2 * S) * (P * P) := by ring
      _ ≤ (2 * S) * 4 :=
        mul_le_mul_of_nonneg_left hPproduct (by positivity)
      _ = 8 * S := by ring
      _ ≤ 8 * C := mul_le_mul_of_nonneg_left hSC (by norm_num)
  have hholder : (2 * T + 2 * S * P) * P ≤ 24 * C := by
    calc
      (2 * T + 2 * S * P) * P = (2 * T) * P + (2 * S * P) * P := by
        rw [add_mul]
      _ ≤ 16 * C + 8 * C := add_le_add hterm₁ hterm₂
      _ = 24 * C := by ring
  change (2 * T + 2 * S * P) * P ≤ (32 * S) / α
  calc
    (2 * T + 2 * S * P) * P ≤ 24 * C := hholder
    _ ≤ 32 * C := by nlinarith only [hC]
    _ = (32 * S) / α := by
      dsimp [C]
      ring

end PDE
