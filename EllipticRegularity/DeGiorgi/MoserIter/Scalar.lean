module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar recursions for the Moser iterations

Standalone real-number lemmas: geometric sums with ratio `γ⁻¹` and the bound on the
infinite products `∏ (A B^n)^{1/e_n}` produced by the Moser iterations.
-/

@[expose] public section

namespace PDE.DGNMMoser

open Finset

/-- A product of the form `∏ (A * B^n)^(1/e n)` is bounded by `A^S₁ * B^S₂` when the
weighted sums of `1/e n` are bounded by `S₁, S₂`. -/
theorem prod_rpow_le (N : ℕ) (e : ℕ → ℝ) {A B S₁ S₂ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h1 : ∑ n ∈ range N, (e n)⁻¹ ≤ S₁)
    (h2 : ∑ n ∈ range N, (n : ℝ) * (e n)⁻¹ ≤ S₂) :
    ∏ n ∈ range N, (A * B ^ n) ^ (e n)⁻¹ ≤ A ^ S₁ * B ^ S₂ := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have key : ∏ n ∈ range N, (A * B ^ n) ^ (e n)⁻¹ =
      A ^ (∑ n ∈ range N, (e n)⁻¹) * B ^ (∑ n ∈ range N, (n : ℝ) * (e n)⁻¹) := by
    rw [Real.rpow_sum_of_pos hA0, Real.rpow_sum_of_pos hB0, ← prod_mul_distrib]
    refine prod_congr rfl fun n _ => ?_
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hB0.le, mul_comm]
  rw [key]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hA h1)
    (Real.rpow_le_rpow_of_exponent_le hB h2) (by positivity) (by positivity)

/-- Partial sums of `γ^{-n}`. -/
theorem sum_inv_pow_le {γ : ℝ} (hγ : 1 < γ) (N : ℕ) :
    ∑ n ∈ range N, (γ ^ n)⁻¹ ≤ γ / (γ - 1) := by
  have hr : ‖γ⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_of_nonneg (by linarith)]
    exact inv_lt_one_of_one_lt₀ hγ
  have hs : Summable (fun n : ℕ => (γ ^ n)⁻¹) := by
    simpa [inv_pow] using summable_geometric_of_norm_lt_one hr
  have := hs.sum_le_tsum (range N) (fun n _ => by positivity)
  refine this.trans (le_of_eq ?_)
  have h2 : ∑' n : ℕ, (γ ^ n)⁻¹ = (1 - γ⁻¹)⁻¹ := by
    simpa [inv_pow] using tsum_geometric_of_norm_lt_one hr
  rw [h2]
  have : γ - 1 ≠ 0 := by linarith
  field_simp

/-- Partial sums of `n γ^{-n}`. -/
theorem sum_nat_mul_inv_pow_le {γ : ℝ} (hγ : 1 < γ) (N : ℕ) :
    ∑ n ∈ range N, (n : ℝ) * (γ ^ n)⁻¹ ≤ γ / (γ - 1) ^ 2 := by
  have hr : ‖γ⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_of_nonneg (by linarith)]
    exact inv_lt_one_of_one_lt₀ hγ
  have hs : Summable (fun n : ℕ => (n : ℝ) * (γ ^ n)⁻¹) := by
    simpa [inv_pow] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have := hs.sum_le_tsum (range N) (fun n _ => by positivity)
  refine this.trans (le_of_eq ?_)
  have h2 : ∑' n : ℕ, (n : ℝ) * (γ ^ n)⁻¹ = γ⁻¹ / (1 - γ⁻¹) ^ 2 := by
    simpa [inv_pow] using tsum_coe_mul_geometric_of_norm_lt_one hr
  rw [h2]
  have : γ - 1 ≠ 0 := by linarith
  have : γ ≠ 0 := by linarith
  field_simp

/-- The product bound for exponents `e n = p₀ γ^n`. -/
theorem prod_geometric_le {γ : ℝ} (hγ : 1 < γ) {p₀ A B : ℝ} (hp : 0 < p₀)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (N : ℕ) :
    ∏ n ∈ range N, (A * B ^ n) ^ (p₀ * γ ^ n)⁻¹ ≤
      A ^ (γ / (γ - 1) / p₀) * B ^ (γ / (γ - 1) ^ 2 / p₀) := by
  refine prod_rpow_le N (fun n => p₀ * γ ^ n) hA hB ?_ ?_
  · have := sum_inv_pow_le hγ N
    calc ∑ n ∈ range N, (p₀ * γ ^ n)⁻¹ = (∑ n ∈ range N, (γ ^ n)⁻¹) / p₀ := by
          rw [sum_div]; exact sum_congr rfl fun n _ => by rw [mul_inv]; ring
      _ ≤ _ := by gcongr
  · have := sum_nat_mul_inv_pow_le hγ N
    calc ∑ n ∈ range N, (n : ℝ) * (p₀ * γ ^ n)⁻¹
        = (∑ n ∈ range N, (n : ℝ) * (γ ^ n)⁻¹) / p₀ := by
          rw [sum_div]; exact sum_congr rfl fun n _ => by rw [mul_inv]; ring
      _ ≤ _ := by gcongr

/-- The product bound for exponents `p, p'γ^0, p'γ^1, …` with `p ≤ p'`. -/
theorem prod_shifted_geometric_le {γ : ℝ} (hγ : 1 < γ) {p p' A B : ℝ} (hp : 0 < p)
    (hpp' : p ≤ p') (hA : 1 ≤ A) (hB : 1 ≤ B) (N : ℕ) :
    ∏ n ∈ range (N + 1), (A * B ^ n) ^ (if n = 0 then p else p' * γ ^ (n - 1))⁻¹ ≤
      A ^ ((1 + γ / (γ - 1)) / p) *
        B ^ ((γ / (γ - 1) + γ / (γ - 1) ^ 2) / p) := by
  have hp' : 0 < p' := lt_of_lt_of_le hp hpp'
  have hγ0 : 0 < γ - 1 := by linarith
  refine prod_rpow_le (N + 1) _ hA hB ?_ ?_
  · rw [sum_range_succ']
    have h1 := sum_inv_pow_le hγ N
    have h3 : ∑ n ∈ range N, (if n + 1 = 0 then p else p' * γ ^ (n + 1 - 1))⁻¹ =
        (∑ n ∈ range N, (γ ^ n)⁻¹) / p' := by
      rw [sum_div]; exact sum_congr rfl fun n _ => by simp [div_eq_mul_inv, mul_comm]
    rw [h3]
    have h4 : (∑ n ∈ range N, (γ ^ n)⁻¹) / p' ≤ γ / (γ - 1) / p := by
      calc _ ≤ (γ / (γ - 1)) / p' := by gcongr
        _ ≤ _ := by gcongr
    simp only [ite_true]
    have : (1 + γ / (γ - 1)) / p = γ / (γ - 1) / p + p⁻¹ := by ring
    rw [this]; linarith
  · rw [sum_range_succ']
    have h1 := sum_inv_pow_le hγ N
    have h2 := sum_nat_mul_inv_pow_le hγ N
    have h3 : ∑ n ∈ range N, ((n + 1 : ℕ) : ℝ) *
        (if n + 1 = 0 then p else p' * γ ^ (n + 1 - 1))⁻¹ =
        (∑ n ∈ range N, (n : ℝ) * (γ ^ n)⁻¹ + ∑ n ∈ range N, (γ ^ n)⁻¹) / p' := by
      rw [← sum_add_distrib, sum_div]
      exact sum_congr rfl fun n _ => by simp; ring
    rw [h3]
    have h4 : (∑ n ∈ range N, (n : ℝ) * (γ ^ n)⁻¹ + ∑ n ∈ range N, (γ ^ n)⁻¹) / p' ≤
        (γ / (γ - 1) + γ / (γ - 1) ^ 2) / p := by
      calc _ ≤ (γ / (γ - 1) ^ 2 + γ / (γ - 1)) / p' := by gcongr
        _ ≤ _ := by rw [add_comm]; gcongr
    simpa using h4

end PDE.DGNMMoser
