module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Scalar forced contraction iteration

This module records the scalar recurrence estimate used by forced geometric
iterations.  It has no geometric or PDE dependencies.
-/

@[expose] public section

namespace PDE

/-- Iterate an affine contraction while retaining the exact finite geometric
sum. -/
theorem forcedIteration_finiteBound
    {X : ℕ → ℝ} {q b : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ n, X (n + 1) ≤ q * X n + b) :
    ∀ n, X n ≤ q ^ n * X 0 + b * ∑ j ∈ Finset.range n, q ^ j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        X (n + 1) ≤ q * X n + b := hstep n
        _ ≤ q * (q ^ n * X 0 + b * ∑ j ∈ Finset.range n, q ^ j) + b :=
          add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
        _ = q ^ (n + 1) * X 0 +
              b * ∑ j ∈ Finset.range (n + 1), q ^ j := by
          calc
            q * (q ^ n * X 0 + b * ∑ j ∈ Finset.range n, q ^ j) + b =
                q ^ (n + 1) * X 0 +
                  b * (q * (∑ j ∈ Finset.range n, q ^ j) + 1) := by
              rw [pow_succ']
              ring
            _ = q ^ (n + 1) * X 0 +
                  b * ∑ j ∈ Finset.range (n + 1), q ^ j := by
              rw [← geom_sum_succ]

/-- A scalar affine recurrence stays below the larger of its initial value
and its fixed point. -/
theorem forcedIteration_le_max
    {X : ℕ → ℝ} {q b : ℝ} (hq : 0 ≤ q) (hq' : q < 1)
    (hstep : ∀ n, X (n + 1) ≤ q * X n + b) :
    ∀ n, X n ≤ max (X 0) (b / (1 - q)) := by
  have hdenom : 0 < 1 - q := sub_pos.mpr hq'
  have hfixed_le : b / (1 - q) ≤ max (X 0) (b / (1 - q)) :=
    le_max_right _ _
  have hfixed_mul : b ≤ max (X 0) (b / (1 - q)) * (1 - q) :=
    (div_le_iff₀ hdenom).mp hfixed_le
  have hstep_bound :
      q * max (X 0) (b / (1 - q)) + b ≤ max (X 0) (b / (1 - q)) := by
    nlinarith [hfixed_mul]
  intro n
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
      calc
        X (n + 1) ≤ q * X n + b := hstep n
        _ ≤ q * max (X 0) (b / (1 - q)) + b :=
          add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
        _ ≤ max (X 0) (b / (1 - q)) := hstep_bound

/-- The geometric contraction `1 - (1 - α) / 8` gives a uniform bound with
all dependence on `α` displayed. -/
theorem forcedIteration_alpha_bound
    {X : ℕ → ℝ} {α b : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hb : 0 ≤ b) (hX0 : 0 ≤ X 0)
    (hstep : ∀ n, X (n + 1) ≤ (1 - (1 - α) / 8) * X n + b) :
    ∀ n, X n ≤ X 0 + 8 * b / (1 - α) := by
  have hq_nonneg : 0 ≤ 1 - (1 - α) / 8 := by
    nlinarith
  have hq_lt_one : 1 - (1 - α) / 8 < 1 := by
    nlinarith
  have hdenom : 1 - (1 - (1 - α) / 8) = (1 - α) / 8 := by
    ring
  have hcap_eq : b / (1 - (1 - (1 - α) / 8)) = 8 * b / (1 - α) := by
    rw [hdenom]
    field_simp [ne_of_gt (sub_pos.mpr hα1)]
  have hcap_nonneg : 0 ≤ 8 * b / (1 - α) :=
    div_nonneg (mul_nonneg (by norm_num) hb) (sub_nonneg.mpr hα1.le)
  intro n
  calc
    X n ≤ max (X 0) (8 * b / (1 - α)) := by
      simpa only [hcap_eq] using
        (forcedIteration_le_max hq_nonneg hq_lt_one hstep n)
    _ ≤ X 0 + 8 * b / (1 - α) := by
      apply max_le
      · linarith [hcap_nonneg]
      · linarith [hX0]

end PDE
