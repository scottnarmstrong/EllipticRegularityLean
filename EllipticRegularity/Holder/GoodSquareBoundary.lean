module

public import PDEFoundation.Sobolev.H1.SquareTrace
public import PDEFoundation.Sobolev.Trace.SquareBoundaryEnergy

/-!
# Quantitative good boundaries for planar `H¹` functions

This module combines the genuine `H¹` square trace, good-radius selection,
and four-side chaining.  The result is the boundary input needed by the
two-dimensional hole-filling argument: one intermediate square has a
continuous trace whose squared boundary oscillation is controlled directly
by the energy in the surrounding dyadic square shell.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

namespace H1Function

/-- Select a square radius `ρ ∈ (r, 2r)` whose continuous four-side trace has
squared boundary oscillation at most `64` times the surrounding shell energy.

The constant is fully exposed: `8 * ρ` comes from the square perimeter
chaining, `4 / r` from fixed-width Fubini radius selection, and `ρ < 2r`
removes the remaining scale. -/
theorem exists_squareSideTrace_with_boundary_sq_oscillation_le_shell
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ ρ, ∃ T : SquareSideTrace u.toFun u.grad x₀ ρ,
      ρ ∈ Ioo r (2 * r) ∧
        T.HasBoundarySqOscillationLE
          (64 * squareShellVectorEnergy u.grad x₀ r) := by
  obtain ⟨ρ, T, hρ, henergy⟩ :=
    exists_squareSideTrace_with_tangential_energy_le hU u hr houter
  have hρpos : 0 < ρ := hr.trans hρ.1
  have hosc :=
    T.hasBoundarySqOscillationLE_actual_tangential_energy hρpos
  have hshell : 0 ≤ squareShellVectorEnergy u.grad x₀ r :=
    integral_nonneg fun _ => vecNormSq_nonneg _
  have hcoefficient : 8 * ρ * (4 / r) ≤ 64 := by
    have hstrict : 32 * ρ / r < 64 := by
      rw [div_lt_iff₀ hr]
      nlinarith [hρ.2]
    calc
      8 * ρ * (4 / r) = 32 * ρ / r := by ring
      _ ≤ 64 := hstrict.le
  have hbound :
      8 * ρ * squareSideTangentialEnergy u.grad x₀ ρ ≤
        64 * squareShellVectorEnergy u.grad x₀ r := by
    calc
      8 * ρ * squareSideTangentialEnergy u.grad x₀ ρ ≤
          8 * ρ * ((4 / r) * squareShellVectorEnergy u.grad x₀ r) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = (8 * ρ * (4 / r)) *
          squareShellVectorEnergy u.grad x₀ r := by ring
      _ ≤ 64 * squareShellVectorEnergy u.grad x₀ r :=
        mul_le_mul_of_nonneg_right hcoefficient hshell
  refine ⟨ρ, T, hρ, ?_⟩
  intro side₁ side₂ s t hs ht
  exact (hosc hs ht).trans hbound

end H1Function

end

end PDE
