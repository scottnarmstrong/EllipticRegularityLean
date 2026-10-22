module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic iteration of an oscillation-decay step

A purely real-analytic statement: an abstract family `Q ρ L` ("the oscillation at
scale `ρ` is at most `L`") which is monotone and which improves by a factor
`θ ≤ 2 ^ (-α)` when the scale is halved, satisfies the Hölder-type bound
`Q r (L₀ * (2 r / ρ₀) ^ α)` at every scale `r ≤ ρ₀`.
-/

@[expose] public section

namespace PDE.DGNMHolder

/-- Iteration of a halving decay step. -/
theorem dyadic_decay_bound {Q : ℝ → ℝ → Prop} {ρ₀ L₀ θ α : ℝ}
    (hρ₀ : 0 < ρ₀) (hL₀ : 0 ≤ L₀) (hθ : 0 ≤ θ) (hα : 0 < α) (hθα : θ ≤ (2 : ℝ) ^ (-α))
    (hmono : ∀ ρ ρ' L L', Q ρ L → 0 < ρ' → ρ' ≤ ρ → L ≤ L' → Q ρ' L')
    (hstep : ∀ ρ L, 0 < ρ → ρ ≤ ρ₀ → Q ρ L → Q (ρ / 2) (θ * L))
    (h0 : Q ρ₀ L₀) :
    ∀ r, 0 < r → r ≤ ρ₀ → Q r (L₀ * (2 * r / ρ₀) ^ α) := by
  have hiter : ∀ j : ℕ, Q (ρ₀ / 2 ^ j) (θ ^ j * L₀) := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      have hle : ρ₀ / 2 ^ j ≤ ρ₀ := by
        apply div_le_self hρ₀.le
        exact one_le_pow₀ (by norm_num)
      have := hstep _ _ (by positivity) hle ih
      rw [show ρ₀ / 2 ^ (j + 1) = ρ₀ / 2 ^ j / 2 by rw [pow_succ]; ring,
        show θ ^ (j + 1) * L₀ = θ * (θ ^ j * L₀) by ring]
      exact this
  intro r hr hrρ
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := ρ₀ / r) (y := (2 : ℝ))
    ((one_le_div hr).2 hrρ) (by norm_num)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hr_le : r ≤ ρ₀ / 2 ^ j := by
    rw [le_div_iff₀ hpow]
    have := (le_div_iff₀ hr).1 hj1
    linarith
  have hr_gt : ρ₀ / 2 ^ (j + 1) < r := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hr).1 hj2
    linarith
  refine hmono _ r _ _ (hiter j) hr hr_le ?_
  -- θ ^ j ≤ (2 r / ρ₀) ^ α
  have h2j : ((2 : ℝ) ^ j)⁻¹ ≤ 2 * r / ρ₀ := by
    rw [le_div_iff₀ hρ₀, inv_mul_eq_div, div_le_iff₀ hpow]
    have : ρ₀ < 2 * r * 2 ^ j := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (j + 1))).1 hr_gt
      rw [pow_succ] at this
      linarith
    linarith
  have hθj : θ ^ j ≤ ((2 : ℝ) ^ j)⁻¹ ^ α := by
    calc θ ^ j ≤ ((2 : ℝ) ^ (-α)) ^ j := pow_le_pow_left₀ hθ hθα j
      _ = (2 : ℝ) ^ (-α * (j : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ = ((2 : ℝ) ^ (-(j : ℝ))) ^ α := by
        rw [← Real.rpow_mul (by norm_num)]
        congr 1
        ring
      _ = ((2 : ℝ) ^ j)⁻¹ ^ α := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  calc θ ^ j * L₀ ≤ ((2 : ℝ) ^ j)⁻¹ ^ α * L₀ := mul_le_mul_of_nonneg_right hθj hL₀
    _ ≤ (2 * r / ρ₀) ^ α * L₀ := by
        apply mul_le_mul_of_nonneg_right _ hL₀
        exact Real.rpow_le_rpow (by positivity) h2j hα.le
    _ = L₀ * (2 * r / ρ₀) ^ α := mul_comm _ _

end PDE.DGNMHolder
