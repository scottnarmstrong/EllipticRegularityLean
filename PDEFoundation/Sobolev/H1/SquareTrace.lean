module

public import PDEFoundation.Sobolev.H1.GoodSquareRadius
public import PDEFoundation.Sobolev.H1.NormalSlices
public import PDEFoundation.Sobolev.Trace.SquareAssembly
public import PDEFoundation.Sobolev.Trace.SquareNormalTrace

/-!
# Common square traces and normal slices for `H¹` functions

This is the public `H¹`-level square-trace theorem for a square selected
inside a convex domain.  The selected radius retains the exact factor `4 / r`
from the good-radius boundary-energy estimate.  The square trace and ACL
normal slices are constructed from one common smooth convex approximation.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

namespace H1Function

/-- An `H¹` function has one square radius and one fixed subsequence of its
smooth convex approximation which jointly construct both the four continuous
side traces and the almost-everywhere canonical normal-slice limits.  The
certificate retains the common sequence, so its endpoint identities are exact
identities of the two canonical uniform limits.  The two displayed energy
bounds retain the exact good-radius factor `4 / r`. -/
theorem exists_squareNormalTraceCertificate_with_tangential_energy_le_enlarged_le_shell
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
        squareSideTangentialEnergy u.grad x₀ ρ ≤
          enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ∧
        enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ≤
          (4 / r) * squareShellVectorEnergy u.grad x₀ r := by
  obtain ⟨k, hkmono, hksmooth, hksum, ρ, hρ, hρenergy, hu, hg, hValueSum,
    hGradientSum, hValueRaw, hGradientRaw⟩ :=
    exists_good_square_radius_summable_convexApproxSmoothW1p_error
      hU u hr houter
  let F : ℕ → Vec 2 → ℝ := fun n =>
    (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
      u.toW1pFunction x₀ hr (k n)).toFun
  have hF : ∀ n, ContDiff ℝ 1 (F n) := by
    intro n
    exact (hksmooth n).of_le (by norm_num)
  have hGradientSum' : Summable (fun n => (2 : ℝ) ^ n *
      enlargedSquareSideScalarEnergy
        (fun x => vecEuclideanNorm (classicalGradient (F n) x - u.grad x))
        x₀ r ρ) := by
    simpa only [F, W1pFunction.convexApproxSmoothW1p_toFun,
      W1pFunction.convexApproxSmoothW1p_grad] using hGradientSum
  have hGradientRaw' : ∀ n, HasRawEnlargedSquareSideSlices
      (fun x => vecEuclideanNorm (classicalGradient (F n) x - u.grad x))
      x₀ r ρ := by
    intro n
    simpa only [F, W1pFunction.convexApproxSmoothW1p_toFun,
      W1pFunction.convexApproxSmoothW1p_grad] using hGradientRaw n
  have hbox : axisBox ![x₀ 0 - ρ, x₀ 1 - ρ]
      ![x₀ 0 + ρ, x₀ 1 + ρ] ⊆ U := by
    intro x hx
    apply houter
    intro i hi
    fin_cases i
    · have hx0 := hx 0 (by simp)
      change x₀ 0 - ρ < x 0 ∧ x 0 < x₀ 0 + ρ at hx0
      change x₀ 0 - 2 * r < x 0 ∧ x 0 < x₀ 0 + 2 * r
      constructor <;> linarith [hx0.1, hx0.2, hρ.2]
    · have hx1 := hx 1 (by simp)
      change x₀ 1 - ρ < x 1 ∧ x 1 < x₀ 1 + ρ at hx1
      change x₀ 1 - 2 * r < x 1 ∧ x 1 < x₀ 1 + 2 * r
      constructor <;> linarith [hx1.1, hx1.2, hρ.2]
  have hnormal : AxisBoxSmoothApproximationData F u.toFun u.grad
      (x₀ 0 - ρ) (x₀ 0 + ρ) (x₀ 1 - ρ) (x₀ 1 + ρ) := by
    simpa only [F] using
      axisBoxSmoothApproximationData_convexApproxSmoothW1p
        hU u hr hbox k hksum
  have htrace : SquareTraceProvenance F u.toFun u.grad x₀ ρ :=
    squareTraceProvenanceOfGoodSmoothData hr hρ hF hu hg
      (by simpa only [F] using hValueSum) hGradientSum'
      (by simpa only [F] using hValueRaw) hGradientRaw'
  let C : SquareNormalTraceCertificate F u.toFun u.grad x₀ ρ := {
    radius_pos := lt_trans hr hρ.1
    traceProvenance := htrace
    normalSliceData := hnormal }
  refine ⟨k, hkmono, ρ, C, hρ,
    squareSideTangentialEnergy_le_enlarged hρ hg, hρenergy⟩

/-- An `H¹` function on a bounded open convex domain has concrete continuous
weak traces on the four sides of one square of radius `ρ ∈ (r, 2r)`.  Its
actual side energy is bounded by the enlarged fixed-width side energy, which
in turn obeys the quantitative good-radius bound with exact factor `4 / r`.

The trace datum is exhibited directly (rather than merely asserted
nonempty), so every stored continuity, a.e.-representative, weak-derivative,
sidewise `L²`, and corner-compatibility field is produced by the smooth
approximation and the genuine Fubini slices. -/
theorem exists_squareSideTrace_with_tangential_energy_le_enlarged_le_shell
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ ρ, ∃ _ : SquareSideTrace u.toFun u.grad x₀ ρ, ρ ∈ Ioo r (2 * r) ∧
      squareSideTangentialEnergy u.grad x₀ ρ ≤
          enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ∧
        enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ≤
          (4 / r) * squareShellVectorEnergy u.grad x₀ r := by
  obtain ⟨k, hkmono, ρ, C, hρ, hactual, henlarged⟩ :=
    exists_squareNormalTraceCertificate_with_tangential_energy_le_enlarged_le_shell
      hU u hr houter
  exact ⟨ρ, (C.traceProvenance).trace, hρ, hactual, henlarged⟩

/-- The enlarged fixed-width side energy at the selected trace radius obeys
the exact good-radius factor `4 / r`. -/
theorem exists_squareSideTrace_with_enlargedSquare_tangential_energy_le
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ ρ, ∃ _ : SquareSideTrace u.toFun u.grad x₀ ρ, ρ ∈ Ioo r (2 * r) ∧
      enlargedSquareSideTangentialEnergy u.grad x₀ r ρ ≤
        (4 / r) * squareShellVectorEnergy u.grad x₀ r := by
  obtain ⟨ρ, T, hρ, -, henlarged⟩ :=
    exists_squareSideTrace_with_tangential_energy_le_enlarged_le_shell
      hU u hr houter
  exact ⟨ρ, T, hρ, henlarged⟩

/-- The actual four-side tangential energy at the selected trace radius
obeys the exact good-radius factor `4 / r`. -/
theorem exists_squareSideTrace_with_tangential_energy_le
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) {x₀ : Vec 2} {r : ℝ}
    (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U) :
    ∃ ρ, ∃ _ : SquareSideTrace u.toFun u.grad x₀ ρ, ρ ∈ Ioo r (2 * r) ∧
      squareSideTangentialEnergy u.grad x₀ ρ ≤
        (4 / r) * squareShellVectorEnergy u.grad x₀ r := by
  obtain ⟨ρ, T, hρ, hactual, henlarged⟩ :=
    exists_squareSideTrace_with_tangential_energy_le_enlarged_le_shell
      hU u hr houter
  exact ⟨ρ, T, hρ, hactual.trans henlarged⟩

end H1Function

end

end PDE
