module

public import PDEFoundation.Euler.OsgoodComparison

/-!
# The Yudovich/Osgood integral lemma

Pure real analysis for Step 5 of the proof of Proposition 3.12: if `0 ≤ y ≤ B²` is integrable on
`[s, t₀]` and `y t ≤ ∫_s^t K p B^(2/p) y^(1 - 1/p)` for all `t` and all `p ≥ 2`, then
`y t ≤ (K (t - s))^p B²`, hence `y = 0` as long as `K (t - s) ≤ 1/2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

/-- The Osgood bound `y t ≤ (K (t - s))^p B²` for every `p ≥ 2`. -/
theorem osgood_yudovich_bound {y : ℝ → ℝ} {s t₀ K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hy0 : ∀ t ∈ Icc s t₀, 0 ≤ y t) (hyB : ∀ t ∈ Icc s t₀, y t ≤ B ^ 2)
    (hyi : IntervalIntegrable y volume s t₀)
    (h : ∀ p : ℝ, 2 ≤ p → ∀ t ∈ Icc s t₀,
      y t ≤ ∫ τ in s..t, K * p * B ^ (2 / p) * y τ ^ (1 - 1 / p)) :
    ∀ p : ℝ, 2 ≤ p → ∀ t ∈ Icc s t₀, y t ≤ (K * (t - s)) ^ p * B ^ 2 := by
  intro p hp t ht
  have hp0 : 0 < p := by linarith
  have h1 := osgood_bound (a := K * p * B ^ (2 / p)) (C := B ^ 2) (by linarith) 
    (mul_nonneg (mul_nonneg hK hp0.le) (Real.rpow_nonneg hB _)) hy0 hyB hyi
    (by simpa [one_div] using h p hp) t ht
  refine h1.trans (le_of_eq ?_)
  have hts : 0 ≤ t - s := sub_nonneg.2 ht.1
  have e : K * p * B ^ (2 / p) * (t - s) / p = (K * (t - s)) * B ^ (2 / p) := by
    field_simp
  rw [e, Real.mul_rpow (mul_nonneg hK hts) (Real.rpow_nonneg hB _), ← Real.rpow_mul hB]
  have : 2 / p * p = ((2 : ℕ) : ℝ) := by push_cast; field_simp
  rw [this, Real.rpow_natCast]

/-- **Yudovich/Osgood lemma.** `y` vanishes on `[s, t₀]` as long as `K (t - s) ≤ 1/2`. -/
theorem osgood_yudovich {y : ℝ → ℝ} {s t₀ K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hy0 : ∀ t ∈ Icc s t₀, 0 ≤ y t) (hyB : ∀ t ∈ Icc s t₀, y t ≤ B ^ 2)
    (hyi : IntervalIntegrable y volume s t₀)
    (h : ∀ p : ℝ, 2 ≤ p → ∀ t ∈ Icc s t₀,
      y t ≤ ∫ τ in s..t, K * p * B ^ (2 / p) * y τ ^ (1 - 1 / p)) :
    ∀ t ∈ Icc s t₀, K * (t - s) ≤ 1 / 2 → y t = 0 := by
  intro t ht hKt
  have hb := osgood_yudovich_bound hK hB hy0 hyB hyi h
  have hts : 0 ≤ t - s := sub_nonneg.2 ht.1
  have hlim : Tendsto (fun p : ℝ => (1 / 2 : ℝ) ^ p * B ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_atTop_of_base_lt_one (1 / 2 : ℝ) (by norm_num) (by norm_num)).mul_const (B ^ 2)
  refine le_antisymm ?_ (hy0 t ht)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
  refine (hb p hp t ht).trans ?_
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_nonneg hK hts) hKt (by linarith)) (sq_nonneg B)

end PDE
