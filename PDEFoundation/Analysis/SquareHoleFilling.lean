module

public import PDEFoundation.Analysis.HoleFilling
public import PDEFoundation.Geometry.SquareShell
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Scalar square-shell hole-filling algebra

This module connects the geometry-free hole-filling recurrence to the exact
partition of an open square into a closed inner square and its dyadic shell.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Exact integral decomposition of the outer open square into the closed
inner square and the dyadic square shell. -/
theorem integral_closedCenteredAxisCube_add_dyadicSquareShell_eq
    (x₀ : Vec 2) {r : ℝ} (hr : 0 < r)
    {e : Vec 2 → ℝ} (he : IntegrableOn e (centeredAxisCube x₀ (2 * r))) :
    (∫ x in closedCenteredAxisCube x₀ r, e x) +
        ∫ x in dyadicSquareShell x₀ r, e x =
      ∫ x in centeredAxisCube x₀ (2 * r), e x := by
  have hIO :
      closedCenteredAxisCube x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    closedCenteredAxisCube_subset_centeredAxisCube_two x₀ hr
  have hImeas : MeasurableSet (closedCenteredAxisCube x₀ r) :=
    (isClosed_closedCenteredAxisCube x₀ r).measurableSet
  have hsplit := integral_inter_add_sdiff
    (s := centeredAxisCube x₀ (2 * r))
    (t := closedCenteredAxisCube x₀ r) hImeas he
  simpa only [Set.inter_eq_right.mpr hIO, dyadicSquareShell] using hsplit

/-- Convert a square-shell filling bound into the exact contraction on the
outer square. -/
theorem integral_closedCenteredAxisCube_le_holeFillingRatio_outer
    (x₀ : Vec 2) {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    {e : Vec 2 → ℝ} (he : IntegrableOn e (centeredAxisCube x₀ (2 * r)))
    (hfill :
      (∫ x in closedCenteredAxisCube x₀ r, e x) ≤
        K * ∫ x in dyadicSquareShell x₀ r, e x) :
    (∫ x in closedCenteredAxisCube x₀ r, e x) ≤
      holeFillingRatio K *
        ∫ x in centeredAxisCube x₀ (2 * r), e x := by
  have hsplit :=
    integral_closedCenteredAxisCube_add_dyadicSquareShell_eq x₀ hr he
  apply inner_le_holeFillingRatio_mul_outer hK
  nlinarith [hsplit]

end PDE
