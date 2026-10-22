module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The scale sum of Step 5

`Σ_k 2⁻ᵏ min (1, e² exp (-(τ - K (k + 1)) a)) ≤ C exp (-θ τ)`.
-/

@[expose] public section

namespace PDE.JohnNirenbergBall

open Real

/-- Pointwise splitting of the `k`-th term. -/
theorem term_le (a K τ : ℝ) (ha : 0 < a) (hK : 0 < K) (_hτ : 0 ≤ τ) (k : ℕ) :
    (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a))) ≤
      (exp 2 * exp (-(a / 2 * τ))) * (1 / 2) ^ k +
        (4 / 3 * exp (-(1 / (8 * K) * τ))) * (2 / 3) ^ k := by
  have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
  have hkey : (1 / 2 : ℝ) ^ k * exp ((1 / (4 * K)) * (K * (k + 1))) ≤ 4 / 3 * (2 / 3) ^ k := by
    have h1 : (1 / (4 * K)) * (K * (k + 1)) = (k + 1) / 4 := by field_simp
    rw [h1]
    have hexp : exp (1 / 4 : ℝ) ≤ 4 / 3 := by
      have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
      rw [Real.exp_neg] at h
      have hpos := Real.exp_pos (1 / 4 : ℝ)
      have h3 : 3 / 4 ≤ 1 / rexp (1 / 4) := by rw [one_div]; linarith
      rw [le_div_iff₀ hpos] at h3
      linarith
    have : exp (((k : ℝ) + 1) / 4) = exp (1 / 4) * exp (1 / 4) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [this]
    have hpow : exp (1 / 4 : ℝ) ^ k ≤ (4 / 3) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le hexp k
    calc (1 / 2 : ℝ) ^ k * (exp (1 / 4) * exp (1 / 4) ^ k)
        = exp (1 / 4) * ((1 / 2) ^ k * exp (1 / 4) ^ k) := by ring
      _ ≤ 4 / 3 * ((1 / 2) ^ k * (4 / 3) ^ k) := by gcongr
      _ = 4 / 3 * (2 / 3) ^ k := by rw [← mul_pow]; norm_num
  by_cases hk : K * (k + 1) ≤ τ / 2
  · have hle : min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a))) ≤ exp 2 * exp (-(a / 2 * τ)) := by
      refine (min_le_right _ _).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos 2).le
      have := mul_le_mul_of_nonneg_right (show τ / 2 ≤ τ - K * (k + 1) by linarith) ha.le
      linarith
    calc (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a)))
        ≤ (1 / 2) ^ k * (exp 2 * exp (-(a / 2 * τ))) := by gcongr
      _ = (exp 2 * exp (-(a / 2 * τ))) * (1 / 2) ^ k := by ring
      _ ≤ _ := by
        have : 0 ≤ (4 / 3 * exp (-(1 / (8 * K) * τ))) * (2 / 3 : ℝ) ^ k := by positivity
        linarith
  · push Not at hk
    have hle : min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a))) ≤
        exp ((1 / (4 * K)) * (K * (k + 1))) * exp (-(1 / (8 * K) * τ)) := by
      refine (min_le_left _ _).trans ?_
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : (1 / (4 * K)) * (K * (k + 1)) - 1 / (8 * K) * τ = (K * (k + 1) - τ / 2) / (4 * K) := by
        field_simp; ring
      have h0 : 0 ≤ (K * (k + 1) - τ / 2) / (4 * K) :=
        div_nonneg (by linarith) (by positivity)
      linarith
    calc (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a)))
        ≤ (1 / 2) ^ k * (exp ((1 / (4 * K)) * (K * (k + 1))) * exp (-(1 / (8 * K) * τ))) := by
          gcongr
      _ = ((1 / 2) ^ k * exp ((1 / (4 * K)) * (K * (k + 1)))) * exp (-(1 / (8 * K) * τ)) := by ring
      _ ≤ (4 / 3 * (2 / 3) ^ k) * exp (-(1 / (8 * K) * τ)) := by gcongr
      _ = (4 / 3 * exp (-(1 / (8 * K) * τ))) * (2 / 3) ^ k := by ring
      _ ≤ _ := by
        have : 0 ≤ (exp 2 * exp (-(a / 2 * τ))) * (1 / 2 : ℝ) ^ k := by positivity
        linarith

theorem series_bound (a K τ : ℝ) (ha : 0 < a) (hK : 0 < K) (hτ : 0 ≤ τ) :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a)))) ∧
    ∑' k : ℕ, (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a))) ≤
      (2 * exp 2 + 4) * exp (-(min (a / 2) (1 / (8 * K)) * τ)) := by
  have hs1 : Summable (fun k : ℕ => (exp 2 * exp (-(a / 2 * τ))) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs2 : Summable (fun k : ℕ => (4 / 3 * exp (-(1 / (8 * K) * τ))) * (2 / 3 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnn : ∀ k : ℕ, 0 ≤ (1 / 2 : ℝ) ^ k * min 1 (exp 2 * exp (-((τ - K * (k + 1)) * a))) :=
    fun k => mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
  have hsum := hs1.add hs2
  refine ⟨Summable.of_nonneg_of_le hnn (fun k => term_le a K τ ha hK hτ k) hsum, ?_⟩
  refine (Summable.tsum_le_tsum (fun k => term_le a K τ ha hK hτ k)
    (Summable.of_nonneg_of_le hnn (fun k => term_le a K τ ha hK hτ k) hsum) hsum).trans ?_
  rw [Summable.tsum_add hs1 hs2, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num),
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hθ1 : exp (-(a / 2 * τ)) ≤ exp (-(min (a / 2) (1 / (8 * K)) * τ)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left (a / 2) (1 / (8 * K))) hτ
    linarith
  have hθ2 : exp (-(1 / (8 * K) * τ)) ≤ exp (-(min (a / 2) (1 / (8 * K)) * τ)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right (a / 2) (1 / (8 * K))) hτ
    linarith
  have e1 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have e2 : (1 - (2 / 3 : ℝ))⁻¹ = 3 := by norm_num
  rw [e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left hθ1 (Real.exp_pos 2).le, hθ2]

end PDE.JohnNirenbergBall
