module

public import PDEFoundation.Analysis.Inequalities.Bombieri.Moment

/-!
# The one-step estimate of the Bombieri-Giusti lemma

For `δ ≤ σ' < σ ≤ 1`, with `κ = c (σ - σ')⁻ᵐ`, the positive part of the logarithm of the norm
satisfies `h σ' ≤ (3/4) h σ + 2c(2κ)⁴ + α₁⁻¹ log (2κ)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {X : Type*} [MeasurableSpace X]

/-- The positive part of the logarithm of an extended nonnegative real, with `log ⊤ = log 0 = 0`. -/
noncomputable def logPlus (x : ℝ≥0∞) : ℝ := max (Real.log x.toReal) 0

theorem max_log_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    max (Real.log a) 0 ≤ max (Real.log b) 0 := by
  rcases ha.eq_or_lt with rfl | hpos
  · simp
  · exact max_le_max (Real.log_le_log hpos hab) le_rfl

/-- Real-variable choice of the exponent `α` in the one-step argument. -/
theorem choose_alpha (c κ α1 L : ℝ) (hc : 1 ≤ c) (hκ : 1 ≤ κ) (hα1 : 0 < α1)
    (hL : 2 * c * (2 * κ) ^ 4 < L) :
    ∃ α : ℝ, 0 < α ∧ α ≤ α1 ∧ α * L ≤ Real.log (L / 2 / c) ∧
      Real.log (2 * κ) / α ≤ α1⁻¹ * Real.log (2 * κ) + L / 4 := by
  have hc0 : 0 < c := by linarith
  have h2κ4 : 1 ≤ (2 * κ) ^ 4 := one_le_pow₀ (by linarith)
  have hl2 : 0 ≤ Real.log (2 * κ) := Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ α1⁻¹ * Real.log (2 * κ) := mul_nonneg (inv_nonneg.mpr hα1.le) hl2
  have hLκ0 : 0 ≤ 2 * c * (2 * κ) ^ 4 := by positivity
  have hLpos : 0 < L := lt_of_le_of_lt hLκ0 hL
  have hlc : (2 * κ) ^ 4 < L / 2 / c := by
    rw [lt_div_iff₀ hc0]; linarith
  have hlogq : 4 * Real.log (2 * κ) < Real.log (L / 2 / c) := by
    have := Real.log_lt_log (by positivity) hlc
    rwa [Real.log_pow] at this
  have hlp : 0 < Real.log (L / 2 / c) := by linarith
  refine ⟨min α1 (Real.log (L / 2 / c) / L), lt_min hα1 (div_pos hlp hLpos), min_le_left _ _, ?_, ?_⟩
  · calc min α1 (Real.log (L / 2 / c) / L) * L ≤ Real.log (L / 2 / c) / L * L := by
          gcongr; exact min_le_right _ _
      _ = _ := by field_simp
  · rcases le_total α1 (Real.log (L / 2 / c) / L) with h | h
    · rw [min_eq_left h, div_eq_inv_mul]; linarith
    · have h4 : Real.log (2 * κ) / (Real.log (L / 2 / c) / L) ≤ L / 4 := by
        rw [div_div_eq_mul_div, div_le_iff₀ hlp]
        linarith [mul_le_mul_of_nonneg_left hlogq.le hLpos.le]
      rw [min_eq_right h]
      linarith

/-- Real-variable form of the moment sum estimate. -/
theorem moment_sum (c α L : ℝ) (hc : 0 < c) (hL : 0 < L) (_hα : 0 < α)
    (hαL : α * L ≤ Real.log (L / 2 / c)) (_hlam : c < L / 2) :
    Real.exp (α * (L / 2)) + Real.exp L ^ α * (c / (L / 2)) ^ (1 / 2 : ℝ) ≤
      2 * Real.exp (α * L / 2) := by
  have hlam0 : 0 < L / 2 := by positivity
  have hexp1 : Real.exp (α * (L / 2)) = Real.exp (α * L / 2) := by ring_nf
  have hrpos : 0 < (L / 2 / c) ^ (1 / 2 : ℝ) := by positivity
  have hexpt : Real.exp (α * L / 2) ≤ (L / 2 / c) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    linarith
  have hinv : (c / (L / 2)) ^ (1 / 2 : ℝ) = ((L / 2 / c) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow (by positivity), inv_div]
  have hprod : Real.exp (α * L / 2) * (c / (L / 2)) ^ (1 / 2 : ℝ) ≤ 1 := by
    rw [hinv, ← div_eq_mul_inv, div_le_one hrpos]; exact hexpt
  have hNα : Real.exp L ^ α = Real.exp (α * L / 2) * Real.exp (α * L / 2) := by
    rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
  rw [hexp1, hNα]
  have := Real.exp_pos (α * L / 2)
  nlinarith [mul_le_mul_of_nonneg_left hprod this.le]

/-- The one-step estimate. -/
theorem one_step (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x) (T' T T1 : Set X)
    (hT : MeasurableSet T) (hT'T : T' ⊆ T) (hTT1 : T ⊆ T1)
    (c κ α₀ : ℝ) (hα₀ : 0 < α₀) (hc : 1 ≤ c) (hκ : 1 ≤ κ)
    (hlog : ∀ lam : ℝ, 0 < lam →
      ν (T1 ∩ {x | lam < Real.log (f x)}) ≤ ENNReal.ofReal (c / lam))
    (hrh : ∀ α : ℝ, 0 < α → α ≤ min 1 (α₀ / 2) →
      eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T') ≤
        ENNReal.ofReal (κ ^ (1 / α - 1 / α₀)) * eLpNorm f (ENNReal.ofReal α) (ν.restrict T))
    (hfin : eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T) < ∞) :
    logPlus (eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T')) ≤
      3 / 4 * logPlus (eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T)) + 2 * c * (2 * κ) ^ 4 +
        (min 1 (α₀ / 2))⁻¹ * Real.log (2 * κ) := by
  set α1 := min 1 (α₀ / 2) with hα1def
  have hα1 : 0 < α1 := lt_min one_pos (by linarith)
  have hc0 : 0 < c := by linarith
  have hκ0 : 0 < κ := by linarith
  set E := eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T) with hE
  set E' := eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T') with hE'
  have hEE' : E' ≤ E := eLpNorm_mono_measure f (Measure.restrict_mono hT'T le_rfl)
  have hEtop : E ≠ ⊤ := hfin.ne
  set N := E.toReal with hNdef
  have hEN : E = ENNReal.ofReal N := (ENNReal.ofReal_toReal hEtop).symm
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hN'N : E'.toReal ≤ N := ENNReal.toReal_mono hEtop hEE'
  have hN'0 : 0 ≤ E'.toReal := ENNReal.toReal_nonneg
  have hl2 : 0 ≤ Real.log (2 * κ) := Real.log_nonneg (by linarith)
  have hR0 : 0 ≤ α1⁻¹ * Real.log (2 * κ) := mul_nonneg (inv_nonneg.mpr hα1.le) hl2
  have h2κ4 : 1 ≤ (2 * κ) ^ 4 := one_le_pow₀ (by linarith)
  have hLκ0 : 0 ≤ 2 * c * (2 * κ) ^ 4 := by positivity
  have hEpl : logPlus E = max (Real.log N) 0 := rfl
  have hE'pl : logPlus E' = max (Real.log E'.toReal) 0 := rfl
  rw [hEpl, hE'pl]
  by_cases hcase : Real.log N ≤ 2 * c * (2 * κ) ^ 4
  · have h1 := max_log_mono hN'0 hN'N
    have h2 : max (Real.log N) 0 ≤ 2 * c * (2 * κ) ^ 4 := max_le hcase hLκ0
    have h3 : 0 ≤ max (Real.log N) 0 := le_max_right _ _
    linarith
  · push Not at hcase
    set L := Real.log N with hLdef
    have hLpos : 0 < L := lt_of_le_of_lt hLκ0 hcase
    have hN1 : 1 < N := (Real.log_pos_iff hN0).mp hLpos
    have hNpos : 0 < N := by linarith
    have hNexp : N = Real.exp L := (Real.exp_log hNpos).symm
    have hlamc : c < L / 2 := by
      have : c ≤ c * (2 * κ) ^ 4 := le_mul_of_one_le_right hc0.le h2κ4
      linarith
    have hcl : c / (L / 2) ≤ 1 := (div_le_one (by positivity)).mpr hlamc.le
    obtain ⟨α, hαpos, hαα1, hαL, hkey⟩ := choose_alpha c κ α1 L hc hκ hα1 hcase
    have h2α : 2 * α ≤ α₀ := by
      have : α1 ≤ α₀ / 2 := min_le_right _ _
      linarith
    have hmom := moment_bound ν f hf hpos T T1 hT hTT1 c hc0.le hlog α₀ α (L / 2) N hN0 hαpos h2α
      (by positivity) hcl hEN
    set t := α * L / 2 with ht
    have hsum : Real.exp (α * (L / 2)) + N ^ α * (c / (L / 2)) ^ (1 / 2 : ℝ) ≤
        2 * Real.exp t := by
      rw [hNexp]; exact moment_sum c α L hc0 hLpos hαpos hαL hlamc
    have hmom2 := hmom.trans (ENNReal.ofReal_le_ofReal hsum)
    set e1 := eLpNorm f (ENNReal.ofReal α) (ν.restrict T) with he1
    have he1b : e1 ≤ ENNReal.ofReal ((2 * Real.exp t) ^ (1 / α)) := by
      have h1 : e1 = (e1 ^ α) ^ (1 / α) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hαpos.ne', ENNReal.rpow_one]
      rw [h1, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      exact ENNReal.rpow_le_rpow hmom2 (by positivity)
    set B := κ ^ (1 / α - 1 / α₀) * (2 * Real.exp t) ^ (1 / α) with hB
    have hBpos : 0 < B := by positivity
    have hE'B : E' ≤ ENNReal.ofReal B := by
      calc E' ≤ ENNReal.ofReal (κ ^ (1 / α - 1 / α₀)) * e1 := hrh α hαpos hαα1
        _ ≤ ENNReal.ofReal (κ ^ (1 / α - 1 / α₀)) *
            ENNReal.ofReal ((2 * Real.exp t) ^ (1 / α)) := by gcongr
        _ = ENNReal.ofReal B := by
          rw [hB, ENNReal.ofReal_mul (by positivity)]
    have hN'B : E'.toReal ≤ B := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE'B
      rwa [ENNReal.toReal_ofReal hBpos.le] at this
    have hlogB : Real.log B ≤ Real.log (2 * κ) / α + L / 2 := by
      have hlk : 0 ≤ Real.log κ := Real.log_nonneg hκ
      have hinvα : 1 / α₀ ≥ 0 := by positivity
      rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow hκ0,
        Real.log_rpow (by positivity), Real.log_mul (by norm_num) (Real.exp_pos t).ne',
        Real.log_exp, Real.log_mul (by norm_num) hκ0.ne', ht]
      have : 1 / α * (Real.log 2 + α * L / 2) = Real.log 2 / α + L / 2 := by field_simp
      have h3 : (1 / α - 1 / α₀) * Real.log κ ≤ 1 / α * Real.log κ := by nlinarith
      rw [this]
      have : Real.log (2) / α + 1 / α * Real.log κ = (Real.log 2 + Real.log κ) / α := by ring
      linarith
    have hmaxL : max L 0 = L := max_eq_left hLpos.le
    rw [hmaxL]
    have h6 : max (Real.log E'.toReal) 0 ≤ max (Real.log B) 0 := max_log_mono hN'0 hN'B
    have h8 : Real.log B ≤ 3 / 4 * L + 2 * c * (2 * κ) ^ 4 + α1⁻¹ * Real.log (2 * κ) := by
      linarith only [hlogB, hkey, hLκ0]
    have h9 : (0 : ℝ) ≤ 3 / 4 * L + 2 * c * (2 * κ) ^ 4 + α1⁻¹ * Real.log (2 * κ) := by
      linarith only [hLpos, hLκ0, hR0]
    exact h6.trans (max_le h8 h9)

end PDE.Bombieri
