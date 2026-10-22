module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Dyadic layer-cake estimates

Two elementary `ℝ≥0∞` facts used in the Step 1 proof of the Sobolev--Poincaré inequality on
normalized convex domains: a dyadic layer-cake upper bound for `∫ v^q`, and the inequality
`ℓ^q ≤ ℓ^1` for a series of extended nonnegative reals.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

/-- The dyadic layer-cake upper bound
`∫ v^q ≤ ∑_k 2^{(k+2)q} μ{v ≥ 2^{k+1}}` for a nonnegative a.e. measurable `v`. -/
theorem lintegral_ofReal_rpow_le_tsum_dyadic {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {v : α → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hv : AEMeasurable v μ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x, ENNReal.ofReal (v x) ^ q ∂μ ≤
      ∑' k : ℤ, ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q * μ {x | (2 : ℝ) ^ (k + 1) ≤ v x} := by
  have hnull : ∀ k : ℤ, NullMeasurableSet {x | (2 : ℝ) ^ (k + 1) ≤ v x} μ := fun k =>
    nullMeasurableSet_le aemeasurable_const hv
  have hpt : ∀ x, ENNReal.ofReal (v x) ^ q ≤ ∑' k : ℤ,
      ({x | (2 : ℝ) ^ (k + 1) ≤ v x}.indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q)) x := by
    intro x
    rcases (hv0 x).eq_or_lt with h0 | hpos
    · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq]
      exact zero_le
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hpos (one_lt_two : (1 : ℝ) < 2)
    have hk : n - 1 + 1 = n := by ring
    have hk2 : n - 1 + 2 = n + 1 := by ring
    refine le_trans ?_ (ENNReal.le_tsum (n - 1))
    have hmem : x ∈ {x | (2 : ℝ) ^ (n - 1 + 1) ≤ v x} := by
      simp only [mem_ofPred_eq, hk]; exact hn1
    rw [Set.indicator_of_mem hmem, hk2]
    gcongr
  calc ∫⁻ x, ENNReal.ofReal (v x) ^ q ∂μ
      ≤ ∫⁻ x, ∑' k : ℤ, ({x | (2 : ℝ) ^ (k + 1) ≤ v x}.indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q)) x ∂μ := lintegral_mono hpt
    _ = ∑' k : ℤ, ∫⁻ x, ({x | (2 : ℝ) ^ (k + 1) ≤ v x}.indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (k + 2)) ^ q)) x ∂μ := by
      refine lintegral_tsum fun k => ?_
      exact aemeasurable_const.indicator₀ (hnull k)
    _ = _ := by
      refine tsum_congr fun k => ?_
      rw [lintegral_indicator_const₀ (hnull k)]

/-- `ℓ^q ≤ ℓ^1` for series of extended nonnegative reals, `q ≥ 1`. -/
theorem tsum_rpow_le_rpow_tsum {ι : Type*} (a : ι → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    ∑' i, a i ^ q ≤ (∑' i, a i) ^ q := by
  set S := ∑' i, a i with hS
  by_cases hT : S = ∞
  · rw [hT, ENNReal.top_rpow_of_pos (by linarith)]; exact le_top
  have hle : ∀ i, a i ≤ S := fun i => ENNReal.le_tsum i
  have hq0 : (0 : ℝ) ≤ q - 1 := by linarith
  have hsplit : ∀ x : ℝ≥0∞, x ^ q = x * x ^ (q - 1) := fun x => by
    conv_lhs => rw [show q = 1 + (q - 1) by ring, ENNReal.rpow_add_of_nonneg _ _ zero_le_one hq0,
      ENNReal.rpow_one]
  calc ∑' i, a i ^ q = ∑' i, a i * a i ^ (q - 1) := tsum_congr fun i => hsplit _
    _ ≤ ∑' i, a i * S ^ (q - 1) := ENNReal.tsum_le_tsum fun i => by gcongr; exact hle i
    _ = S * S ^ (q - 1) := ENNReal.tsum_mul_right
    _ = S ^ q := (hsplit S).symm

end PDE
