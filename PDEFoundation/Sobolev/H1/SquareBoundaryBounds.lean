module

public import PDEFoundation.Sobolev.H1.SquareTrace
public import PDEFoundation.Sobolev.Trace.SquareBoundaryBounds

/-!
# Quantitative boundary bounds for selected `H¹` square traces

This module composes the common square trace/normal-slice certificate with
the actual four-side energy estimate.  The resulting squared boundary
oscillation is bounded by `64` times the original square-shell energy.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

namespace H1Function

/-- The common square trace selected from an `H¹` function has squared
boundary oscillation at most `64` times the original shell energy.  The same
certificate and both intermediate tangential-energy bounds are retained. -/
theorem exists_squareNormalTraceCertificate_with_boundarySqOscillationLE
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ ρ,
      ∃ C : SquareNormalTraceCertificate
        (fun n =>
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x₀ hr (k n)).toFun)
        u.toFun u.grad x₀ ρ,
      ρ ∈ Ioo r (2 * r) ∧
        C.traceProvenance.trace.HasBoundarySqOscillationLE
          (64 * squareShellVectorEnergy u.grad x₀ r) ∧
        squareSideTangentialEnergy u.grad x₀ ρ ≤
          enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ∧
        enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ≤
          (4 / r) * squareShellVectorEnergy u.grad x₀ r := by
  obtain ⟨k, hk, ρ, C, hρ, hactual, henlarged⟩ :=
    u.exists_squareNormalTraceCertificate_with_tangential_energy_le_enlarged_le_shell
      hU hr houter
  have hshell : 0 ≤ squareShellVectorEnergy u.grad x₀ r := by
    exact integral_nonneg fun x => vecNormSq_nonneg (u.grad x)
  have hboundary :
      C.traceProvenance.trace.HasBoundarySqOscillationLE
        (64 * squareShellVectorEnergy u.grad x₀ r) :=
    C.traceProvenance.trace
      |>.hasBoundarySqOscillationLE_shell_of_tangential_energy_le
        hr C.radius_pos hρ.2.le hshell (hactual.trans henlarged)
  exact ⟨k, hk, ρ, C, hρ, hboundary, hactual, henlarged⟩

end H1Function

end

end PDE
