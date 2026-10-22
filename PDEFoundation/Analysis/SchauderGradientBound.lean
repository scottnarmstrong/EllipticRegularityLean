module

public import PDEFoundation.Analysis.SchauderGradientIteration

/-!
# Explicit exponent dependence in the gradient iteration

The two geometric denominators in the finite iteration are bounded here by
the actual exponent gaps. The coefficient term is absorbed without adding
another factor of `1 / (1 - α)` to the initial energy.
-/

@[expose] public section

namespace PDE

/-- Explicit finite-scale bounds with the source exponent dependence. -/
theorem schauderGradientIteration_explicit_bound
    {E m M : ℕ → ℝ} {α a b D : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hE0 : 0 ≤ E 0) (hm0 : 0 ≤ m 0)
    (hE : ∀ n, E (n + 1) ≤ (2 : ℝ) ^ (α - 1) * E n + a * M n + b)
    (hm : ∀ n, m (n + 1) ≤ m n + D * ((2 : ℝ) ^ (-α)) ^ n * E n)
    (hM : ∀ n, M n ≤ m n + ((2 : ℝ) ^ (-α)) ^ n * E n)
    (hsmall : a ≤ α * (1 - α) / (32 * (1 + D))) :
    ∀ n,
      E n ≤ 8 * (E 0 + m 0 + b / (1 - α)) ∧
      M n ≤ (40 * (1 + D) / α) * (E 0 + m 0 + b / (1 - α)) := by
  have hg : 0 < 1 - α := sub_pos.mpr hα1
  have hqgap := one_sub_two_rpow_neg_ge_div_four hg
    (by linarith only [hα0] : 1 - α < 1)
  rw [show -(1 - α) = α - 1 by ring] at hqgap
  have htgap := one_sub_two_rpow_neg_ge_div_four hα0 hα1
  have hqpos : 0 < 1 - (2 : ℝ) ^ (α - 1) :=
    lt_of_lt_of_le (by positivity) hqgap
  have htpos : 0 < 1 - (2 : ℝ) ^ (-α) :=
    lt_of_lt_of_le (by positivity) htgap
  have hDpos : 0 < 1 + D := by positivity
  have hasmall : a ≤ (1 - α) / 4 := by
    calc
      a ≤ α * (1 - α) / (32 * (1 + D)) := hsmall
      _ ≤ α * (1 - α) / 32 :=
        div_le_div_of_nonneg_left (mul_nonneg hα0.le hg.le)
          (by norm_num) (by linarith only [hD])
      _ ≤ (1 - α) / 4 := by
        have hh := mul_le_mul_of_nonneg_right hα1.le hg.le
        linarith only [hh, hg]
  have haq : a / (1 - (2 : ℝ) ^ (α - 1)) ≤ 1 := by
    apply (div_le_one hqpos).mpr
    exact hasmall.trans hqgap
  have hbq : b / (1 - (2 : ℝ) ^ (α - 1)) ≤ 4 * (b / (1 - α)) := by
    calc
      b / (1 - (2 : ℝ) ^ (α - 1)) ≤ b / ((1 - α) / 4) :=
        div_le_div_of_nonneg_left hb (by positivity) hqgap
      _ = 4 * (b / (1 - α)) := by field_simp
  have hL : 2 * (E 0 + (a * m 0 + b) / (1 - (2 : ℝ) ^ (α - 1))) ≤
      8 * (E 0 + m 0 + b / (1 - α)) := by
    have ham := mul_le_mul_of_nonneg_right haq hm0
    rw [one_mul] at ham
    have hforcing : (a * m 0 + b) / (1 - (2 : ℝ) ^ (α - 1)) ≤
        m 0 + 4 * (b / (1 - α)) := by
      rw [add_div, mul_div_right_comm]
      exact add_le_add ham hbq
    linarith only [hforcing, hE0, hm0]
  have hH : 1 + D / (1 - (2 : ℝ) ^ (-α)) ≤ 4 * (1 + D) / α := by
    have hratio : D / (1 - (2 : ℝ) ^ (-α)) ≤ 4 * D / α := by
      calc
        D / (1 - (2 : ℝ) ^ (-α)) ≤ D / (α / 4) :=
          div_le_div_of_nonneg_left hD (by positivity) htgap
        _ = 4 * D / α := by ring
    have hbase : 1 ≤ 4 / α := (le_div_iff₀ hα0).mpr
      (by linarith only [hα1])
    calc
      1 + D / (1 - (2 : ℝ) ^ (-α)) ≤ 4 / α + 4 * D / α :=
        add_le_add hbase hratio
      _ = 4 * (1 + D) / α := by ring
  let S := E 0 + m 0 + b / (1 - α)
  have hS : 0 ≤ S := add_nonneg (add_nonneg hE0 hm0) (div_nonneg hb hg.le)
  have hmS : m 0 ≤ S := by
    dsimp only [S]
    linarith only [hE0, div_nonneg hb hg.le]
  have hfac : 1 ≤ (1 + D) / α := (le_div_iff₀ hα0).mpr
    (by linarith only [hα1, hD])
  have hmfac : m 0 ≤ ((1 + D) / α) * S :=
    hmS.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac hS)
  have hbound := schauderGradientIteration_finite_bound hα0 hα1 ha hb hD
    hE0 hm0 hE hm hM hsmall
  intro n
  refine ⟨(hbound n).1.trans hL, ?_⟩
  calc
    M n ≤ m 0 + (1 + D / (1 - (2 : ℝ) ^ (-α))) *
        (2 * (E 0 + (a * m 0 + b) / (1 - (2 : ℝ) ^ (α - 1)))) := (hbound n).2
    _ ≤ ((1 + D) / α) * S + (4 * (1 + D) / α) * (8 * S) := by
      apply add_le_add hmfac
      exact mul_le_mul hH hL (by positivity) (by positivity)
    _ = (33 * (1 + D) / α) * S := by ring
    _ ≤ (40 * (1 + D) / α) * S := by
      apply mul_le_mul_of_nonneg_right _ hS
      exact div_le_div_of_nonneg_right
        (by linarith only [hDpos]) hα0.le

end PDE
