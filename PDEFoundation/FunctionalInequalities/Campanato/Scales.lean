module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Geometric chaining over dyadic scales

Abstract real-variable lemmas: if a function `M` of the scale changes by at most `c ρ ^ α` between
comparable scales `ρ / 2 ≤ ρ' ≤ ρ < 1 / 4`, then it changes by at most `c ρ ^ α / (1 - 2 ^ (-α))`
between any two scales, and has a limit at `0` along dyadic scales.
-/

@[expose] public section

namespace PDE.CampanatoProof

open Filter Topology

/-- The geometric ratio `2 ^ (-α)` is in `(0, 1)`. -/
theorem two_rpow_neg_lt_one {α : ℝ} (hα : 0 < α) : (2 : ℝ) ^ (-α) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem half_rpow {α ρ : ℝ} (hρ : 0 ≤ ρ) : (ρ / 2) ^ α = ρ ^ α * (2 : ℝ) ^ (-α) := by
  rw [Real.div_rpow hρ (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]

/-- Chaining step: induction on the number of dyadic scales between `ρ'` and `ρ`. -/
theorem scale_chain_aux {M : ℝ → ℝ} {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (h1 : ∀ ρ ρ', 0 < ρ → ρ < 1 / 4 → ρ / 2 ≤ ρ' → ρ' ≤ ρ → |M ρ' - M ρ| ≤ c * ρ ^ α) :
    ∀ n : ℕ, ∀ ρ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ → ρ < 1 / 4 → ρ / 2 ^ (n + 1) < ρ' →
      |M ρ' - M ρ| ≤ c * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) := by
  have hq1 := two_rpow_neg_lt_one hα
  have hq0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := by linarith
  intro n
  induction n with
  | zero =>
    intro ρ ρ' hρ' hle hρ4 hlt
    have hρ : 0 < ρ := lt_of_lt_of_le hρ' hle
    refine (h1 ρ ρ' hρ hρ4 (by simp at hlt; linarith) hle).trans ?_
    rw [le_div_iff₀ hden]
    have : 0 ≤ c * ρ ^ α := mul_nonneg hc (Real.rpow_nonneg hρ.le _)
    nlinarith
  | succ n ih =>
    intro ρ ρ' hρ' hle hρ4 hlt
    have hρ : 0 < ρ := lt_of_lt_of_le hρ' hle
    by_cases hhalf : ρ / 2 ≤ ρ'
    · refine (h1 ρ ρ' hρ hρ4 hhalf hle).trans ?_
      rw [le_div_iff₀ hden]
      have : 0 ≤ c * ρ ^ α := mul_nonneg hc (Real.rpow_nonneg hρ.le _)
      nlinarith
    · replace hhalf := not_le.mp hhalf
      have hih := ih (ρ / 2) ρ' hρ' hhalf.le (by linarith) (by
        have : ρ / 2 / 2 ^ (n + 1) = ρ / 2 ^ (n + 1 + 1) := by
          rw [pow_succ 2 (n + 1)]; field_simp
        rw [this]; exact hlt)
      have hstep := h1 ρ (ρ / 2) hρ hρ4 le_rfl (by linarith)
      calc |M ρ' - M ρ| = |(M ρ' - M (ρ / 2)) + (M (ρ / 2) - M ρ)| := by ring_nf
        _ ≤ |M ρ' - M (ρ / 2)| + |M (ρ / 2) - M ρ| := abs_add_le _ _
        _ ≤ c * (ρ / 2) ^ α / (1 - (2 : ℝ) ^ (-α)) + c * ρ ^ α := add_le_add hih hstep
        _ = c * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) := by
          rw [half_rpow hρ.le]
          field_simp
          ring

/-- Any two scales `ρ' ≤ ρ < 1/4` have `|M ρ' - M ρ| ≤ c ρ ^ α / (1 - 2 ^ (-α))`. -/
theorem scale_chain {M : ℝ → ℝ} {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (h1 : ∀ ρ ρ', 0 < ρ → ρ < 1 / 4 → ρ / 2 ≤ ρ' → ρ' ≤ ρ → |M ρ' - M ρ| ≤ c * ρ ^ α)
    {ρ ρ' : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) (hρ4 : ρ < 1 / 4) :
    |M ρ' - M ρ| ≤ c * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hρ' hle
  obtain ⟨N, hN⟩ := exists_nat_gt (ρ / ρ')
  have hN2 : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : 0 < (2 : ℝ) ^ N := by positivity
  refine scale_chain_aux hc hα h1 N ρ ρ' hρ' hle hρ4 ?_
  rw [div_lt_iff₀ (by positivity)]
  have : ρ < N * ρ' := (div_lt_iff₀ hρ').mp hN
  have h3 : ρ' * N < ρ' * 2 ^ N := mul_lt_mul_of_pos_left hN2 hρ'
  rw [pow_succ]
  nlinarith

/-- Dyadic scales `1/8 / 2^n`. -/
noncomputable def dyadicScale (n : ℕ) : ℝ := (1 / 8) / 2 ^ n

theorem dyadicScale_pos (n : ℕ) : 0 < dyadicScale n := by unfold dyadicScale; positivity

theorem dyadicScale_lt (n : ℕ) : dyadicScale n < 1 / 4 := by
  unfold dyadicScale
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem dyadicScale_anti {m n : ℕ} (h : m ≤ n) : dyadicScale n ≤ dyadicScale m := by
  unfold dyadicScale
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_right₀ (by norm_num) h

theorem tendsto_dyadicScale : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall dyadicScale_pos)
  exact tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Existence of the limit along dyadic scales, with the quantitative bound at every scale. -/
theorem exists_scale_limit {M : ℝ → ℝ} {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (h1 : ∀ ρ ρ', 0 < ρ → ρ < 1 / 4 → ρ / 2 ≤ ρ' → ρ' ≤ ρ → |M ρ' - M ρ| ≤ c * ρ ^ α) :
    ∃ L : ℝ, Tendsto (fun n => M (dyadicScale n)) atTop (𝓝 L) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 4 → |L - M ρ| ≤ c * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) := by
  have hq1 := two_rpow_neg_lt_one hα
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := by linarith
  have hcauchy : CauchySeq (fun n => M (dyadicScale n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * (c * dyadicScale N ^ α / (1 - (2 : ℝ) ^ (-α))))
      ?_ ?_
    · intro n m N hn hm
      rw [Real.dist_eq]
      have ha := scale_chain hc hα h1 (dyadicScale_pos n) (dyadicScale_anti hn)
        (dyadicScale_lt N)
      have hb := scale_chain hc hα h1 (dyadicScale_pos m) (dyadicScale_anti hm)
        (dyadicScale_lt N)
      calc |M (dyadicScale n) - M (dyadicScale m)|
          = |(M (dyadicScale n) - M (dyadicScale N)) - (M (dyadicScale m) - M (dyadicScale N))| := by
            ring_nf
        _ ≤ |M (dyadicScale n) - M (dyadicScale N)| + |M (dyadicScale m) - M (dyadicScale N)| :=
            abs_sub _ _
        _ ≤ _ := by linarith
    · have hρ : Tendsto (fun N => dyadicScale N ^ α) atTop (𝓝 0) := by
        have := (tendsto_dyadicScale.mono_right nhdsWithin_le_nhds).rpow_const
          (Or.inr hα.le)
        simpa [Real.zero_rpow hα.ne'] using this
      have := ((hρ.const_mul c).div_const (1 - (2 : ℝ) ^ (-α))).const_mul 2
      simpa using this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, hL, fun ρ hρ hρ4 => ?_⟩
  have hev : ∀ᶠ n in atTop, |M (dyadicScale n) - M ρ| ≤ c * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) := by
    filter_upwards [tendsto_dyadicScale.eventually (Ioo_mem_nhdsGT hρ)] with n hn
    exact scale_chain hc hα h1 (dyadicScale_pos n) hn.2.le hρ4
  exact le_of_tendsto ((hL.sub_const (M ρ)).abs) hev

end PDE.CampanatoProof
