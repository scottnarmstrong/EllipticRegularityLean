module

public import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement
public import PDEFoundation.Sobolev.Trace.Square

/-!
# Quantitative increments of square-side traces

Each continuous side in `SquareSideTrace` is the actual one-dimensional
`H¹` representative selected by the trace construction.  The four results
below expose its sharp constant-one squared increment estimate.  Every side
is parametrized by its increasing Cartesian coordinate, so no orientation
sign appears in the derivative.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

namespace SquareSideTrace

/-- Sharp squared increment control along the right side. -/
theorem right_sq_abs_increment_le
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {ρ : ℝ}
    (T : SquareSideTrace u g x₀ ρ) (hρ : 0 < ρ)
    {s t : ℝ} (hs : s ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ))
    (ht : t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) (hst : s ≤ t) :
    |T.right t - T.right s| ^ 2 ≤
      (t - s) * ∫ z in Icc s t,
        |squareLoopRightTangentialRestriction g x₀ ρ z| ^ (2 : ℝ) :=
  ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
    (by linarith) T.rightContinuous T.rightMemL2
      T.rightTangentialMemL2 T.rightWeakDeriv hs ht hst

/-- Sharp squared increment control along the left side. -/
theorem left_sq_abs_increment_le
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {ρ : ℝ}
    (T : SquareSideTrace u g x₀ ρ) (hρ : 0 < ρ)
    {s t : ℝ} (hs : s ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ))
    (ht : t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) (hst : s ≤ t) :
    |T.left t - T.left s| ^ 2 ≤
      (t - s) * ∫ z in Icc s t,
        |squareLoopLeftTangentialRestriction g x₀ ρ z| ^ (2 : ℝ) :=
  ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
    (by linarith) T.leftContinuous T.leftMemL2
      T.leftTangentialMemL2 T.leftWeakDeriv hs ht hst

/-- Sharp squared increment control along the top side. -/
theorem top_sq_abs_increment_le
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {ρ : ℝ}
    (T : SquareSideTrace u g x₀ ρ) (hρ : 0 < ρ)
    {s t : ℝ} (hs : s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ))
    (ht : t ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) (hst : s ≤ t) :
    |T.top t - T.top s| ^ 2 ≤
      (t - s) * ∫ z in Icc s t,
        |squareLoopTopTangentialRestriction g x₀ ρ z| ^ (2 : ℝ) :=
  ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
    (by linarith) T.topContinuous T.topMemL2
      T.topTangentialMemL2 T.topWeakDeriv hs ht hst

/-- Sharp squared increment control along the bottom side. -/
theorem bottom_sq_abs_increment_le
    {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {x₀ : Vec 2} {ρ : ℝ}
    (T : SquareSideTrace u g x₀ ρ) (hρ : 0 < ρ)
    {s t : ℝ} (hs : s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ))
    (ht : t ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) (hst : s ≤ t) :
    |T.bottom t - T.bottom s| ^ 2 ≤
      (t - s) * ∫ z in Icc s t,
        |squareLoopBottomTangentialRestriction g x₀ ρ z| ^ (2 : ℝ) :=
  ContinuousOn.sq_abs_increment_le_of_hasWeakDerivOnIoo
    (by linarith) T.bottomContinuous T.bottomMemL2
      T.bottomTangentialMemL2 T.bottomWeakDeriv hs ht hst

end SquareSideTrace

end

end PDE
