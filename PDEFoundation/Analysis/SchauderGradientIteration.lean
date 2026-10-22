module

public import PDEFoundation.Analysis.CoupledOscillationIteration
public import PDEFoundation.Regularity.CampanatoConstant

/-!
# Quantitative gaps in the gradient Schauder iteration

The mean telescoping and oscillation contraction each have a geometric gap.
Their product gives the coefficient smallness `α (1 - α)`.
-/

@[expose] public section

namespace PDE

private theorem geometric_feedback_small
    {α g q t a D : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hg : 0 < g)
    (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hgapq : g / 4 ≤ 1 - q) (hgapt : α / 4 ≤ 1 - t)
    (hsmall : a ≤ α * g / (32 * (1 + D))) :
    a * (1 + D / (1 - t)) ≤ (1 - q) / 2 := by
  have hratio : D / (1 - t) ≤ 4 * D / α := by
    calc
      D / (1 - t) ≤ D / (α / 4) :=
        div_le_div_of_nonneg_left hD (by positivity) hgapt
      _ = 4 * D / α := by ring
  have hH : 1 + D / (1 - t) ≤ 4 * (1 + D) / α := by
    have hbase : 1 ≤ 4 / α := (le_div_iff₀ hα0).mpr (by linarith only [hα1])
    calc
      1 + D / (1 - t) ≤ 4 / α + 4 * D / α := add_le_add hbase hratio
      _ = 4 * (1 + D) / α := by ring
  calc
    a * (1 + D / (1 - t)) ≤ a * (4 * (1 + D) / α) :=
      mul_le_mul_of_nonneg_left hH ha
    _ ≤ (α * g / (32 * (1 + D))) * (4 * (1 + D) / α) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = g / 8 := by
      have hDne : 1 + D ≠ 0 := ne_of_gt (by positivity)
      field_simp [hα0.ne', hDne]
      norm_num
    _ ≤ (1 - q) / 2 := by linarith only [hgapq]

/-- The coefficient threshold proportional to `α(1-α)` discharges the
finite iteration's feedback condition for the actual dyadic factors. -/
theorem schauderGradientIteration_small_feedback
    {α a D : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hsmall : a ≤ α * (1 - α) / (32 * (1 + D))) :
    a * (1 + D / (1 - (2 : ℝ) ^ (-α))) ≤
      (1 - (2 : ℝ) ^ (α - 1)) / 2 := by
  have hgapq := one_sub_two_rpow_neg_ge_div_four
    (sub_pos.mpr hα1) (by linarith only [hα0] : 1 - α < 1)
  rw [show -(1 - α) = α - 1 by ring] at hgapq
  exact geometric_feedback_small hα0 hα1.le (sub_pos.mpr hα1) hD ha
    hgapq (one_sub_two_rpow_neg_ge_div_four hα0 hα1) hsmall

/-- Uniform finite-depth bounds for the actual weighted dyadic oscillation
and mean-size recurrences. No finiteness of an infinite supremum is used. -/
theorem schauderGradientIteration_finite_bound
    {E m M : ℕ → ℝ} {α a b D : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hE0 : 0 ≤ E 0) (hm0 : 0 ≤ m 0)
    (hE : ∀ n, E (n + 1) ≤ (2 : ℝ) ^ (α - 1) * E n + a * M n + b)
    (hm : ∀ n, m (n + 1) ≤ m n + D * ((2 : ℝ) ^ (-α)) ^ n * E n)
    (hM : ∀ n, M n ≤ m n + ((2 : ℝ) ^ (-α)) ^ n * E n)
    (hsmall : a ≤ α * (1 - α) / (32 * (1 + D))) :
    ∀ n,
      E n ≤ 2 * (E 0 + (a * m 0 + b) / (1 - (2 : ℝ) ^ (α - 1))) ∧
      M n ≤ m 0 + (1 + D / (1 - (2 : ℝ) ^ (-α))) *
        (2 * (E 0 + (a * m 0 + b) / (1 - (2 : ℝ) ^ (α - 1)))) := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (α - 1) := Real.rpow_nonneg (by norm_num) _
  have ht0 : 0 ≤ (2 : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (α - 1) < 1 := by
    have hgap := one_sub_two_rpow_neg_ge_div_four
      (sub_pos.mpr hα1) (by linarith only [hα0] : 1 - α < 1)
    rw [show -(1 - α) = α - 1 by ring] at hgap
    linarith only [hgap, sub_pos.mpr hα1]
  have ht1 : (2 : ℝ) ^ (-α) < 1 := by
    have hgap := one_sub_two_rpow_neg_ge_div_four hα0 hα1
    linarith only [hgap, hα0]
  exact coupledOscillationIteration_small_feedback hq0 hq1 ht0 ht1 ha hb hD hE0 hm0
    hE hm hM (schauderGradientIteration_small_feedback hα0 hα1 hD ha hsmall)

end PDE
