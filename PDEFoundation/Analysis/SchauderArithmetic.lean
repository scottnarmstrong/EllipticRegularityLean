module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Scalar arithmetic for the Schauder contraction

This module isolates the exponential and polynomial estimates behind the
small-oscillation contraction. It has no geometric or PDE dependencies.
-/

@[expose] public section

namespace PDE

/-- Pure polynomial factor estimate used after the exponential comparison. -/
private theorem schauder_linear_product_bound
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 + x / 4 ≤ (1 - x / 8) * (1 + x / 2) := by
  have hprod : 0 ≤ x * (1 - x) :=
    mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hx_sq : x ^ 2 ≤ x := by
    nlinarith [hprod]
  nlinarith [hx_sq]

/-- On the unit interval, the dyadic power dominates the linear factor needed
for the Schauder contraction. -/
theorem one_add_quarter_le_one_sub_eighth_mul_two_rpow
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 + x / 4 ≤ (1 - x / 8) * (2 : ℝ) ^ x := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hlog' :=
      Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  have harg : x / 2 ≤ Real.log 2 * x := by
    calc
      x / 2 = x * (1 / 2) := by ring
      _ ≤ x * Real.log 2 := mul_le_mul_of_nonneg_left hlog hx.1
      _ = Real.log 2 * x := by ring
  have hexp_tangent : Real.log 2 * x + 1 ≤ Real.exp (Real.log 2 * x) :=
    Real.add_one_le_exp _
  have hpow : 1 + x / 2 ≤ (2 : ℝ) ^ x := by
    calc
      1 + x / 2 ≤ Real.log 2 * x + 1 := by linarith only [harg]
      _ ≤ Real.exp (Real.log 2 * x) := hexp_tangent
      _ = (2 : ℝ) ^ x := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlinear := schauder_linear_product_bound hx
  have hfactor : 0 ≤ 1 - x / 8 := by
    nlinarith only [hx.1, hx.2]
  calc
    1 + x / 4 ≤ (1 - x / 8) * (1 + x / 2) := hlinear
    _ ≤ (1 - x / 8) * (2 : ℝ) ^ x :=
      mul_le_mul_of_nonneg_left hpow hfactor

/-- The manuscript smallness threshold gives exactly the contraction factor
`1 - (1 - α) / 8`; no additional loss is introduced. -/
theorem schauder_smallness_implies_contraction
    {d : ℕ} {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : δ ≤ (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) :
    (1 + 2 * δ * (2 : ℝ) ^ ((d : ℝ) / 2)) *
        (1 / 2 : ℝ) ^ (1 - α) ≤ 1 - (1 - α) / 8 := by
  let x : ℝ := 1 - α
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [x]
    constructor <;> linarith
  have hDpos : 0 < D := by
    dsimp only [D]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hpower_cancel :
      (2 : ℝ) ^ (-3 - (d : ℝ) / 2) *
          (2 : ℝ) ^ ((d : ℝ) / 2) = 1 / 8 := by
    calc
      (2 : ℝ) ^ (-3 - (d : ℝ) / 2) *
          (2 : ℝ) ^ ((d : ℝ) / 2) =
          (2 : ℝ) ^ ((-3 - (d : ℝ) / 2) + (d : ℝ) / 2) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = (2 : ℝ) ^ (-3 : ℝ) := by
        congr 1
        ring
      _ = 1 / 8 := by norm_num
  have hdelta_term : 2 * δ * D ≤ x / 4 := by
    calc
      2 * δ * D ≤ 2 * ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)) * D :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ (by norm_num)) hDpos.le
      _ = 2 * (1 - α) *
          ((2 : ℝ) ^ (-3 - (d : ℝ) / 2) * D) := by ring
      _ = x / 4 := by
        rw [hpower_cancel]
        dsimp only [x]
        ring
  have hbracket : 1 + 2 * δ * D ≤ 1 + x / 4 := by
    linarith only [hdelta_term]
  have hhalf_pos : 0 < (1 / 2 : ℝ) ^ x :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) x
  have hhalf_cancel :
      (2 : ℝ) ^ x * (1 / 2 : ℝ) ^ x = 1 := by
    have hhalf_eq : (1 / 2 : ℝ) ^ x = (2 : ℝ) ^ (-x) := by
      calc
        (1 / 2 : ℝ) ^ x = ((2 : ℝ)⁻¹) ^ x := by
          congr 1
          norm_num
        _ = (2 : ℝ) ^ (-x) := by
          rw [← Real.rpow_neg_eq_inv_rpow (2 : ℝ) x]
    rw [hhalf_eq, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_inv_cancel₀
      (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x))
  have hscaled :
      (1 + x / 4) * (1 / 2 : ℝ) ^ x ≤ 1 - x / 8 := by
    calc
      (1 + x / 4) * (1 / 2 : ℝ) ^ x ≤
          ((1 - x / 8) * (2 : ℝ) ^ x) * (1 / 2 : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right
          (one_add_quarter_le_one_sub_eighth_mul_two_rpow hx) hhalf_pos.le
      _ = 1 - x / 8 := by
        rw [mul_assoc, hhalf_cancel, mul_one]
  calc
    (1 + 2 * δ * (2 : ℝ) ^ ((d : ℝ) / 2)) *
        (1 / 2 : ℝ) ^ (1 - α) =
        (1 + 2 * δ * D) * (1 / 2 : ℝ) ^ x := by
          dsimp only [D, x]
    _ ≤ (1 + x / 4) * (1 / 2 : ℝ) ^ x :=
      mul_le_mul_of_nonneg_right hbracket hhalf_pos.le
    _ ≤ 1 - x / 8 := hscaled
    _ = 1 - (1 - α) / 8 := by dsimp only [x]

end PDE
