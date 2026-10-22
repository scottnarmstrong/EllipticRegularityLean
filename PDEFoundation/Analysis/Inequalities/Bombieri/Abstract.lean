module

public import PDEFoundation.Analysis.Inequalities.Bombieri.OneStep
public import PDEFoundation.Analysis.Inequalities.Bombieri.Iteration

/-!
# The abstract Bombieri-Giusti lemma (Lemma 1.12)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {X : Type*} [MeasurableSpace X]

/-- The constant of the Bombieri-Giusti lemma, depending only on `δ, α₀, c, m`. -/
noncomputable def giustiConst (δ α₀ c m : ℝ) : ℝ :=
  Real.exp (((32 * c ^ 5 + 2 * (min 1 (α₀ / 2))⁻¹ * c ^ 4) /
      ((1 - δ) * (1 - (1 + (3 / 4 : ℝ) ^ (1 / (4 * m))) / 2)) ^ (4 * m)) /
    (1 - (3 / 4 : ℝ) / ((1 + (3 / 4 : ℝ) ^ (1 / (4 * m))) / 2) ^ (4 * m)))

theorem giustiConst_pos (δ α₀ c m : ℝ) : 0 < giustiConst δ α₀ c m := Real.exp_pos _

/-- The recursive inequality from the one-step estimate. -/
theorem step_to_recursion (c m α1 d : ℝ) (hc : 1 ≤ c) (hm : 0 < m) (hα1 : 0 < α1)
    (hd0 : 0 < d) (hd1 : d ≤ 1) :
    2 * c * (2 * (c * d ^ (-m))) ^ 4 + α1⁻¹ * Real.log (2 * (c * d ^ (-m))) ≤
      (32 * c ^ 5 + 2 * α1⁻¹ * c ^ 4) / d ^ (4 * m) := by
  have hc0 : 0 < c := by linarith
  have hD : 0 < d ^ m := Real.rpow_pos_of_pos hd0 m
  have hD1 : d ^ m ≤ 1 := Real.rpow_le_one hd0.le hd1 hm.le
  have hneg : d ^ (-m) = (d ^ m)⁻¹ := Real.rpow_neg hd0.le m
  have h4 : d ^ (4 * m) = (d ^ m) ^ 4 := by
    rw [mul_comm, Real.rpow_mul hd0.le]
    exact_mod_cast Real.rpow_natCast (d ^ m) 4
  set κ := c * d ^ (-m) with hκ
  have hκ1 : 1 ≤ κ := by
    rw [hκ, hneg, ← div_eq_mul_inv, le_div_iff₀ hD]; nlinarith
  have hκ4 : κ ^ 4 = c ^ 4 / d ^ (4 * m) := by
    rw [hκ, hneg, h4, mul_pow, inv_pow]; ring
  have hlog : Real.log (2 * κ) ≤ 2 * κ ^ 4 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 * κ by positivity)
    have h2 : κ ≤ κ ^ 4 := by
      calc κ = κ ^ 1 := (pow_one κ).symm
        _ ≤ κ ^ 4 := pow_le_pow_right₀ hκ1 (by norm_num)
    linarith
  have hα1' : 0 ≤ α1⁻¹ := inv_nonneg.mpr hα1.le
  calc 2 * c * (2 * κ) ^ 4 + α1⁻¹ * Real.log (2 * κ)
      ≤ 2 * c * (2 * κ) ^ 4 + α1⁻¹ * (2 * κ ^ 4) := by gcongr
    _ = (32 * c ^ 5 + 2 * α1⁻¹ * c ^ 4) / d ^ (4 * m) := by
      rw [show 2 * c * (2 * κ) ^ 4 + α1⁻¹ * (2 * κ ^ 4) =
        (32 * c + 2 * α1⁻¹) * κ ^ 4 by ring, hκ4]
      ring

/-- Exponential of `logPlus` dominates the (real) norm. -/
theorem le_exp_logPlus {E : ℝ≥0∞} (hE : E ≠ ⊤) :
    E ≤ ENNReal.ofReal (Real.exp (logPlus E)) := by
  refine le_trans (ENNReal.ofReal_toReal hE).ge (ENNReal.ofReal_le_ofReal ?_)
  rcases (ENNReal.toReal_nonneg (a := E)).eq_or_lt with h | h
  · rw [← h]; exact (Real.exp_pos _).le
  · calc E.toReal = Real.exp (Real.log E.toReal) := (Real.exp_log h).symm
      _ ≤ Real.exp (logPlus E) := Real.exp_le_exp.mpr (le_max_left _ _)

/-- **Bombieri-Giusti lemma** (Lemma 1.12). -/
theorem bombieri_giusti (δ α₀ c m : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hα₀ : 0 < α₀)
    (hc : 1 ≤ c) (hm : 0 < m)
    (ν : Measure X) [IsProbabilityMeasure ν] (U : ℝ → Set X)
    (hUm : ∀ σ, δ ≤ σ → σ ≤ 1 → MeasurableSet (U σ))
    (hUmono : ∀ σ' σ, δ ≤ σ' → σ' ≤ σ → σ ≤ 1 → U σ' ⊆ U σ)
    (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (hfin : eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U 1)) < ∞)
    (hlog : ∀ lam : ℝ, 0 < lam →
      ν (U 1 ∩ {x | lam < Real.log (f x)}) ≤ ENNReal.ofReal (c / lam))
    (hrh : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (α₀ / 2) →
      eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((c * (σ - σ') ^ (-m)) ^ (1 / α - 1 / α₀)) *
          eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ))) :
    eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U δ)) ≤ ENNReal.ofReal (giustiConst δ α₀ c m) := by
  set α1 := min 1 (α₀ / 2) with hα1def
  have hα1 : 0 < α1 := lt_min one_pos (by linarith)
  set ϑ : ℝ := 3 / 4 with hϑ
  set β : ℝ := 4 * m with hβ
  have hβ0 : 0 < β := by positivity
  have hϑ0 : 0 < ϑ := by norm_num
  have hϑ1 : ϑ < 1 := by norm_num
  set τ : ℝ := (1 + ϑ ^ (1 / β)) / 2 with hτ
  have hr0 : 0 < ϑ ^ (1 / β) := Real.rpow_pos_of_pos hϑ0 _
  have hr1 : ϑ ^ (1 / β) < 1 := Real.rpow_lt_one hϑ0.le hϑ1 (by positivity)
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ < 1 := by rw [hτ]; linarith
  have hrτ : ϑ < τ ^ β := by
    have h1 : ϑ ^ (1 / β) < τ := by rw [hτ]; linarith
    have := Real.rpow_lt_rpow hr0.le h1 hβ0
    rwa [← Real.rpow_mul hϑ0.le, one_div, inv_mul_cancel₀ hβ0.ne', Real.rpow_one] at this
  set K : ℝ := 32 * c ^ 5 + 2 * α1⁻¹ * c ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  set h : ℝ → ℝ := fun σ => logPlus (eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U σ))) with hh
  have hfin' : ∀ σ, δ ≤ σ → σ ≤ 1 →
      eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U σ)) ≠ ⊤ := by
    intro σ h1 h2
    refine ne_top_of_le_ne_top hfin.ne ?_
    exact eLpNorm_mono_measure f (Measure.restrict_mono (hUmono σ 1 h1 h2 le_rfl) le_rfl)
  have hrec : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 →
      h σ' ≤ ϑ * h σ + K / (σ - σ') ^ β := by
    intro σ' σ h1 h2 h3
    have hd0 : 0 < σ - σ' := by linarith
    have hd1 : σ - σ' ≤ 1 := by linarith
    have hDm : (σ - σ') ^ m ≤ 1 := Real.rpow_le_one hd0.le hd1 hm.le
    have hκ1 : 1 ≤ c * (σ - σ') ^ (-m) := by
      rw [Real.rpow_neg hd0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hd0 m)]
      nlinarith
    have hstep := one_step ν f hf hpos (U σ') (U σ) (U 1) (hUm σ (by linarith) h3)
      (hUmono σ' σ h1 h2.le h3) (hUmono σ 1 (by linarith) h3 le_rfl) c (c * (σ - σ') ^ (-m))
      α₀ hα₀ hc hκ1 hlog (hrh σ' σ h1 h2 h3)
      (lt_top_iff_ne_top.mpr (hfin' σ (by linarith) h3))
    have := step_to_recursion c m α1 (σ - σ') hc hm hα1 hd0 hd1
    have hβeq : (σ - σ') ^ β = (σ - σ') ^ (4 * m) := rfl
    show logPlus _ ≤ 3 / 4 * logPlus _ + K / (σ - σ') ^ β
    linarith only [hstep, this, hβeq]
  have hhH : ∀ σ, δ ≤ σ → σ ≤ 1 → h σ ≤ h 1 := by
    intro σ h1 h2
    show max _ _ ≤ max _ _
    apply max_log_mono ENNReal.toReal_nonneg
    exact ENNReal.toReal_mono (hfin' 1 hδ1.le le_rfl)
      (eLpNorm_mono_measure f (Measure.restrict_mono (hUmono σ 1 h1 h2 le_rfl) le_rfl))
  have hit := iteration_bound h δ K ϑ β τ (h 1) hδ1 hτ0 hτ1 hϑ0.le hϑ1 hβ0 hrτ hrec hK0
    (fun σ _ _ => le_max_right _ _) hhH
  have hδσ := hfin' δ le_rfl hδ1.le
  refine (le_exp_logPlus hδσ).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold giustiConst
  exact Real.exp_le_exp.mpr hit

end PDE.Bombieri
