module

public import EllipticRegularity.Parabolic.Cauchy.Weights.Nash

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Optimizing the Nash--Aronson exponent

The large-separation range attains the exact scalar minimum. In the small
range the fixed choice `A = 2 * Λ` costs at most `exp (2 * κ)`, which is a
dimension-only factor when `κ = (d + 2) / 2`.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

/-- A single parameter choice gives the optimized Nash--Aronson rate up to
the dimension-only small-range factor `exp (2κ)`. In the range `κΛ < X`, the
choice attains the exact minimum; otherwise `A = 2Λ` suffices. -/
theorem nashGaussianWeight_rate_with_lowRange_constant {Λ κ X : ℝ}
    (hΛ : 0 < Λ) (hκ : 0 < κ) (hX : 0 ≤ X) :
    ∃ A, Λ < A ∧
      -X / A + κ * A / (A - Λ) ≤
        -X / Λ + 2 * Real.sqrt (κ * X / Λ) + 2 * κ := by
  by_cases hlarge : κ * Λ < X
  · obtain ⟨A, hA, heq⟩ :=
      nashGaussianWeight_optimized_rate_attained hΛ hκ hlarge
    refine ⟨A, hA, ?_⟩
    rw [heq]
    nlinarith
  · let y : ℝ := X / Λ
    have hy0 : 0 ≤ y := div_nonneg hX hΛ.le
    have hyκ : y ≤ κ := by
      dsimp [y]
      apply (div_le_iff₀ hΛ).2
      linarith
    have hyprod : y ^ 2 ≤ κ * y := by
      nlinarith [mul_le_mul_of_nonneg_right hyκ hy0]
    have hsqrt : y ≤ Real.sqrt (κ * y) := by
      exact Real.le_sqrt_of_sq_le hyprod
    have hsmall : -y / 2 ≤ -y + 2 * Real.sqrt (κ * y) := by
      nlinarith
    refine ⟨2 * Λ, by linarith, ?_⟩
    have hrate : -X / (2 * Λ) + κ * (2 * Λ) / (2 * Λ - Λ) = -y / 2 + 2 * κ := by
      dsimp [y]
      field_simp [ne_of_gt hΛ]
      ring
    calc
      -X / (2 * Λ) + κ * (2 * Λ) / (2 * Λ - Λ) = -y / 2 + 2 * κ := hrate
      _ ≤ -y + 2 * Real.sqrt (κ * y) + 2 * κ := by linarith [hsmall]
      _ = -X / Λ + 2 * Real.sqrt (κ * X / Λ) + 2 * κ := by
        have hroot : κ * y = κ * X / Λ := by
          dsimp [y]
          ring
        rw [hroot]
        dsimp [y]
        ring

end PDE.Parabolic.Cauchy.Weights
