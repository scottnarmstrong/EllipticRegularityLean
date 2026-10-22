module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The iteration sum in the local Gehring lemma

Pure real analysis for Step 4 of the proof of the Gehring lemma: if
`a j ≤ T_j ^ ε * (ω * m) + a (j + 1) / 4 + Hh` with
`T_j = (24 √d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m` and `ε` small, then
`a 0 ≤ 4 ω m ^ (1 + ε) + (4 / 3) Hh`.
-/

@[expose] public section

namespace PDE.Gehring

open Filter Topology

/-- Numeric facts: for `(d + 1) ε ≤ 1 / (32 * 3 ^ d * (9 / 2) ^ (d + 1))` one has
`(24 √d) ^ ((d + 1) ε) ≤ 2` and `2 ^ ((d + 1) ε) ≤ 2`. -/
theorem iteration_numeric (d : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ((d : ℝ) + 1) * ε ≤ 1 / (32 * 3 ^ d * ((9 : ℝ) / 2) ^ (d + 1))) :
    (24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) ≤ 2 ∧ (2 : ℝ) ^ (((d : ℝ) + 1) * ε) ≤ 2 := by
  set x : ℝ := ((d : ℝ) + 1) * ε with hx
  have hx0 : 0 ≤ x := by positivity
  have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have hH : (1 : ℝ) ≤ ((9 : ℝ) / 2) ^ (d + 1) := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) < 32 * 3 ^ d * ((9 : ℝ) / 2) ^ (d + 1) := by positivity
  have hx1 : x * (32 * 3 ^ d) ≤ 1 := by
    have := (le_div_iff₀ hden).1 hεd
    nlinarith
  have hxle : x ≤ 1 := by nlinarith
  have hsq : Real.sqrt d ≤ 3 ^ d := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (d : ℝ) < 3 ^ d := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
    nlinarith
  refine ⟨?_, ?_⟩
  · have hy : (0 : ℝ) ≤ 24 * Real.sqrt d := by positivity
    have hb := rpow_one_add_le_one_add_mul_self (s := 24 * Real.sqrt d - 1)
      (by linarith) hx0 hxle
    have : (1 + (24 * Real.sqrt d - 1)) = 24 * Real.sqrt d := by ring
    rw [this] at hb
    have hxy : x * (24 * Real.sqrt d) ≤ 1 := by
      have : x * (24 * Real.sqrt d) ≤ x * (32 * 3 ^ d) := by gcongr; linarith
      linarith
    nlinarith
  · calc (2 : ℝ) ^ x ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hxle
      _ = 2 := Real.rpow_one 2

theorem iteration_term_eq (d j : ℕ) (ε m : ℝ) (hm : 0 ≤ m) :
    ((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε =
      (24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) * ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j * m ^ ε := by
  have h24 : (0 : ℝ) ≤ 24 * Real.sqrt d := by positivity
  rw [Real.mul_rpow (by positivity) hm, Real.mul_rpow (by positivity) (by positivity)]
  congr 2
  · rw [← Real.rpow_natCast, ← Real.rpow_mul h24]; push_cast; rfl
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    push_cast; congr 1; ring

/-- The iteration sum of the manuscript (Step 4 of the proof of the Gehring lemma):
`ω m ^ (1 + ε)` and `Hh` are the two source terms. -/
theorem iteration_sum_le (d : ℕ) {ε m ω Hh K : ℝ} {a : ℕ → ℝ}
    (hε : 0 ≤ ε) (hm : 0 ≤ m) (hω : 0 ≤ ω) (hHh : 0 ≤ Hh)
    (hεd : ((d : ℝ) + 1) * ε ≤ 1 / (32 * 3 ^ d * ((9 : ℝ) / 2) ^ (d + 1)))
    (haK : ∀ j, a j ≤ K)
    (hrec : ∀ j : ℕ, a j ≤
      ((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε * (ω * m)
        + a (j + 1) / 4 + Hh) :
    a 0 ≤ 4 * ω * m ^ (1 + ε) + 4 / 3 * Hh := by
  obtain ⟨hA, hc⟩ := iteration_numeric d hε hεd
  set S : ℝ := 4 * ω * m ^ (1 + ε) with hS
  have hmε : m ^ ε * m = m ^ (1 + ε) := by
    rw [add_comm, Real.rpow_add' hm (by linarith [hε] : ε + 1 ≠ 0) ]
    · simp
  have hS0 : 0 ≤ S := by positivity
  have hb : ∀ j : ℕ, ((24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m) ^ ε * (ω * m)
      ≤ S / 2 * 2 ^ j := by
    intro j
    rw [iteration_term_eq d j ε m hm]
    have hcj : ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j ≤ 2 ^ j := by
      gcongr
    have hA0 : 0 ≤ (24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) := by positivity
    have hc0 : 0 ≤ ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j := by positivity
    have hmm : 0 ≤ m ^ ε := by positivity
    have e : (24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) * ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j *
        m ^ ε * (ω * m) = ((24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) *
        ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j) * (ω * m ^ (1 + ε)) := by
      rw [← hmε]; ring
    rw [e]
    have hq : 0 ≤ ω * m ^ (1 + ε) := by positivity
    have h2 : (24 * Real.sqrt d) ^ (((d : ℝ) + 1) * ε) * ((2 : ℝ) ^ (((d : ℝ) + 1) * ε)) ^ j
        ≤ 2 * 2 ^ j := mul_le_mul hA hcj hc0 (by norm_num)
    calc _ ≤ (2 * 2 ^ j) * (ω * m ^ (1 + ε)) := mul_le_mul_of_nonneg_right h2 hq
      _ = S / 2 * 2 ^ j := by rw [hS]; ring
  have key : ∀ n : ℕ, a 0 ≤ S * (1 - (1 / 2) ^ n) + 4 / 3 * Hh * (1 - (1 / 4) ^ n)
      + (1 / 4) ^ n * a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hrec n
      have h2 := hb n
      have h4 : (0 : ℝ) ≤ (1 / 4) ^ n := by positivity
      have h5 : (1 / 4 : ℝ) ^ n * 2 ^ n = (1 / 2) ^ n := by
        rw [← mul_pow]; norm_num
      have h6 : (1 / 4 : ℝ) ^ n * (a n) ≤ (1 / 4) ^ n * (S / 2 * 2 ^ n + a (n + 1) / 4 + Hh) := by
        apply mul_le_mul_of_nonneg_left _ h4
        linarith
      have e1 : (1 / 4 : ℝ) ^ n * (S / 2 * 2 ^ n + a (n + 1) / 4 + Hh)
          = S / 2 * ((1 / 4) ^ n * 2 ^ n) + (1 / 4) ^ (n + 1) * a (n + 1) + (1 / 4) ^ n * Hh := by
        rw [pow_succ]; ring
      rw [e1, h5] at h6
      rw [pow_succ, pow_succ (1 / 4 : ℝ)] at *
      nlinarith [h6, ih]
  have hlim : Tendsto (fun n : ℕ => S * (1 - 0) + 4 / 3 * Hh * (1 - 0) + (1 / 4 : ℝ) ^ n * K)
      atTop (𝓝 (S * (1 - 0) + 4 / 3 * Hh * (1 - 0) + 0 * K)) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    exact tendsto_const_nhds.add (this.mul_const K)
  have hle : ∀ n : ℕ, a 0 ≤ S * (1 - 0) + 4 / 3 * Hh * (1 - 0) + (1 / 4 : ℝ) ^ n * K := by
    intro n
    have h4 : (0 : ℝ) ≤ (1 / 4) ^ n := by positivity
    have h2 : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have := key n
    have := mul_le_mul_of_nonneg_left (haK n) h4
    nlinarith [mul_nonneg hS0 h2, mul_nonneg hHh h4]
  have := ge_of_tendsto' hlim hle
  linarith

end PDE.Gehring
