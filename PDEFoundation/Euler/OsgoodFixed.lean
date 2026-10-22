module

public import PDEFoundation.Euler.OsgoodGronwall
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Osgood comparison at a fixed exponent

If `0 ≤ y ≤ C` is integrable on `[s, t₀]` and `y t ≤ ∫_s^t a y^(1 - 1/p)` there, then
`y t ≤ (a (t - s) / p)^p`. The proof compares `Z(t) = ∫_s^t a y^(1-1/p)` with the barrier
`(δ^(1/p) + a (t - s)/p)^p - δ` and closes with the derivative-free Gronwall lemma.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

/-- One-sided Lipschitz bound for `x ↦ x ^ r`, `0 ≤ r ≤ 1`, on `[δ, ∞)`. -/
theorem rpow_sub_rpow_le {r δ w u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (hw : δ ≤ w) (hwu : w ≤ u) :
    u ^ r - w ^ r ≤ r * δ ^ (r - 1) * (u - w) := by
  have hw0 : 0 < w := hδ.trans_le hw
  have hu0 : 0 ≤ u := hw0.le.trans hwu
  have hb : (1 + (u / w - 1)) ^ r ≤ 1 + r * (u / w - 1) :=
    rpow_one_add_le_one_add_mul_self (by have : 0 ≤ u / w := div_nonneg hu0 hw0.le; linarith) hr0 hr1
  have h1 : u ^ r = w ^ r * (1 + (u / w - 1)) ^ r := by
    rw [← Real.mul_rpow hw0.le (by have : 0 ≤ u / w := div_nonneg hu0 hw0.le; linarith)]
    congr 1; field_simp; ring
  have h2 : w ^ r * (r * (u / w - 1)) = r * w ^ (r - 1) * (u - w) := by
    rw [Real.rpow_sub hw0, Real.rpow_one]; field_simp
  have h3 : w ^ (r - 1) ≤ δ ^ (r - 1) :=
    Real.rpow_le_rpow_of_nonpos hδ hw (by linarith)
  have h4 : 0 ≤ r * (u - w) := mul_nonneg hr0 (sub_nonneg.2 hwu)
  calc u ^ r - w ^ r ≤ w ^ r * (1 + r * (u / w - 1)) - w ^ r := by
        rw [h1]; have := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hw0.le r); linarith
    _ = r * w ^ (r - 1) * (u - w) := by rw [← h2]; ring
    _ ≤ r * δ ^ (r - 1) * (u - w) := by
        have := mul_le_mul_of_nonneg_left h3 h4
        calc r * w ^ (r - 1) * (u - w) = r * (u - w) * w ^ (r - 1) := by ring
          _ ≤ r * (u - w) * δ ^ (r - 1) := this
          _ = _ := by ring

/-- The barrier `c(τ) = δ^(1/p) + a (τ - s)/p`. -/
theorem barrier_integral {s a p δ : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hδ : 0 < δ) (t : ℝ)
    (ht : s ≤ t) :
    (∫ τ in s..t, a * ((δ ^ p⁻¹ + a * (τ - s) / p) ^ p) ^ (1 - p⁻¹)) =
      (δ ^ p⁻¹ + a * (t - s) / p) ^ p - δ := by
  have hp0 : 0 < p := by linarith
  have hcpos : ∀ τ ∈ Set.uIcc s t, 0 < δ ^ p⁻¹ + a * (τ - s) / p := by
    intro τ hτ
    rw [Set.uIcc_of_le ht] at hτ
    have : 0 ≤ a * (τ - s) / p := div_nonneg (mul_nonneg ha (sub_nonneg.2 hτ.1)) hp0.le
    have := Real.rpow_pos_of_pos hδ p⁻¹
    linarith
  have hderiv : ∀ τ ∈ Set.uIcc s t,
      HasDerivAt (fun τ => (δ ^ p⁻¹ + a * (τ - s) / p) ^ p)
        (a * ((δ ^ p⁻¹ + a * (τ - s) / p) ^ p) ^ (1 - p⁻¹)) τ := by
    intro τ hτ
    have h0 : HasDerivAt (fun τ : ℝ => δ ^ p⁻¹ + a * (τ - s) / p) (a / p) τ := by
      have := (((hasDerivAt_id τ).sub_const s).const_mul a).div_const p |>.const_add (δ ^ p⁻¹)
      simpa using this
    have h1 := h0.rpow_const (p := p) (Or.inl (hcpos τ hτ).ne')
    have hc := (hcpos τ hτ).le
    have : ((δ ^ p⁻¹ + a * (τ - s) / p) ^ p) ^ (1 - p⁻¹)
        = (δ ^ p⁻¹ + a * (τ - s) / p) ^ (p - 1) := by
      rw [← Real.rpow_mul hc]; congr 1; field_simp
    rw [this]
    convert h1 using 1
    field_simp
  have hcont : ContinuousOn (fun τ => a * ((δ ^ p⁻¹ + a * (τ - s) / p) ^ p) ^ (1 - p⁻¹))
      (Set.uIcc s t) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.rpow_const (ContinuousOn.rpow_const (by fun_prop) ?_) ?_
    · intro τ hτ; exact Or.inl (hcpos τ hτ).ne'
    · intro τ _; right; have : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
      linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [sub_self, mul_zero, zero_div, add_zero]
  rw [← Real.rpow_mul hδ.le, inv_mul_cancel₀ (by linarith), Real.rpow_one]

end PDE
