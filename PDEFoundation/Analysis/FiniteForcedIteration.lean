module

public import PDEFoundation.Analysis.ForcedIteration

/-!
# Finite scalar forced iteration

This variant uses an affine recurrence only at the finitely many indices below
the requested terminal index.
-/

@[expose] public section

namespace PDE

/-- Iterate an affine recurrence through `N` using only the steps with index
strictly below `N`. -/
theorem forcedIteration_finiteBound_of_lt
    {X : ℕ → ℝ} {q b : ℝ} {N : ℕ} (hq : 0 ≤ q)
    (hstep : ∀ k < N, X (k + 1) ≤ q * X k + b) :
    X N ≤ q ^ N * X 0 + b * ∑ j ∈ Finset.range N, q ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
      have ih' := ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self N)))
      calc
        X (N + 1) ≤ q * X N + b := hstep N (Nat.lt_succ_self N)
        _ ≤ q * (q ^ N * X 0 + b * ∑ j ∈ Finset.range N, q ^ j) + b :=
          add_le_add (mul_le_mul_of_nonneg_left ih' hq) le_rfl
        _ = q ^ (N + 1) * X 0 +
              b * ∑ j ∈ Finset.range (N + 1), q ^ j := by
          calc
            q * (q ^ N * X 0 + b * ∑ j ∈ Finset.range N, q ^ j) + b =
                q ^ (N + 1) * X 0 +
                  b * (q * (∑ j ∈ Finset.range N, q ^ j) + 1) := by
              rw [pow_succ']
              ring
            _ = q ^ (N + 1) * X 0 +
                  b * ∑ j ∈ Finset.range (N + 1), q ^ j := by
              rw [← geom_sum_succ]

end PDE
