module

public import PDEFoundation.Sobolev.OneDimensional.UniformLimit
public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitive
public import PDEFoundation.Sobolev.Trace.SmoothSides

/-!
# Trace data on the sides of a square

This module records only the concrete data needed to assemble four scalar
side traces.  The side parameters are increasing Cartesian coordinates, not
the oriented time of `squareLoop`: right and left use the vertical coordinate,
while top and bottom use the horizontal coordinate.

No existence construction is performed here.  In particular, deriving this
data from a two-dimensional Sobolev function remains a separate analytic
step.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- The coordinate-one component of a vector field on the right side. -/
def squareLoopRightTangentialRestriction
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => g (squareLoopRightSide x₀ r t) 1

/-- The coordinate-one component of a vector field on the left side. -/
def squareLoopLeftTangentialRestriction
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => g (squareLoopLeftSide x₀ r t) 1

/-- The coordinate-zero component of a vector field on the top side. -/
def squareLoopTopTangentialRestriction
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => g (squareLoopTopSide x₀ r t) 0

/-- The coordinate-zero component of a vector field on the bottom side. -/
def squareLoopBottomTangentialRestriction
    (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  fun t => g (squareLoopBottomSide x₀ r t) 0

/-- The four continuous scalar traces on the closed sides of a square, along
with their genuine sidewise `L²` data, concrete a.e. representatives, weak
derivatives given by the corresponding coordinate of the specified gradient,
and the four corner compatibilities. Every side uses its increasing Cartesian
coordinate as parameter. -/
structure SquareSideTrace
    (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2) (x₀ : Vec 2) (r : ℝ) where
  right : ℝ → ℝ
  left : ℝ → ℝ
  top : ℝ → ℝ
  bottom : ℝ → ℝ
  rightContinuous : ContinuousOn right (Icc (x₀ 1 - r) (x₀ 1 + r))
  leftContinuous : ContinuousOn left (Icc (x₀ 1 - r) (x₀ 1 + r))
  topContinuous : ContinuousOn top (Icc (x₀ 0 - r) (x₀ 0 + r))
  bottomContinuous : ContinuousOn bottom (Icc (x₀ 0 - r) (x₀ 0 + r))
  rightMemL2 : MemLp right 2
    (volume.restrict (Ioo (x₀ 1 - r) (x₀ 1 + r)))
  leftMemL2 : MemLp left 2
    (volume.restrict (Ioo (x₀ 1 - r) (x₀ 1 + r)))
  topMemL2 : MemLp top 2
    (volume.restrict (Ioo (x₀ 0 - r) (x₀ 0 + r)))
  bottomMemL2 : MemLp bottom 2
    (volume.restrict (Ioo (x₀ 0 - r) (x₀ 0 + r)))
  rightAeEq : right =ᵐ[volume.restrict (Ioo (x₀ 1 - r) (x₀ 1 + r))]
    squareLoopRightRestriction u x₀ r
  leftAeEq : left =ᵐ[volume.restrict (Ioo (x₀ 1 - r) (x₀ 1 + r))]
    squareLoopLeftRestriction u x₀ r
  topAeEq : top =ᵐ[volume.restrict (Ioo (x₀ 0 - r) (x₀ 0 + r))]
    squareLoopTopRestriction u x₀ r
  bottomAeEq : bottom =ᵐ[volume.restrict (Ioo (x₀ 0 - r) (x₀ 0 + r))]
    squareLoopBottomRestriction u x₀ r
  rightWeakDeriv : HasWeakDerivOnIoo
    (x₀ 1 - r) (x₀ 1 + r) right
      (squareLoopRightTangentialRestriction g x₀ r)
  leftWeakDeriv : HasWeakDerivOnIoo
    (x₀ 1 - r) (x₀ 1 + r) left
      (squareLoopLeftTangentialRestriction g x₀ r)
  topWeakDeriv : HasWeakDerivOnIoo
    (x₀ 0 - r) (x₀ 0 + r) top
      (squareLoopTopTangentialRestriction g x₀ r)
  bottomWeakDeriv : HasWeakDerivOnIoo
    (x₀ 0 - r) (x₀ 0 + r) bottom
      (squareLoopBottomTangentialRestriction g x₀ r)
  rightTangentialMemL2 :
    MemLp (squareLoopRightTangentialRestriction g x₀ r) 2
      (volume.restrict (Icc (x₀ 1 - r) (x₀ 1 + r)))
  leftTangentialMemL2 :
    MemLp (squareLoopLeftTangentialRestriction g x₀ r) 2
      (volume.restrict (Icc (x₀ 1 - r) (x₀ 1 + r)))
  topTangentialMemL2 :
    MemLp (squareLoopTopTangentialRestriction g x₀ r) 2
      (volume.restrict (Icc (x₀ 0 - r) (x₀ 0 + r)))
  bottomTangentialMemL2 :
    MemLp (squareLoopBottomTangentialRestriction g x₀ r) 2
      (volume.restrict (Icc (x₀ 0 - r) (x₀ 0 + r)))
  rightTop : right (x₀ 1 + r) = top (x₀ 0 + r)
  topLeft : top (x₀ 0 - r) = left (x₀ 1 + r)
  leftBottom : left (x₀ 1 - r) = bottom (x₀ 0 - r)
  bottomRight : bottom (x₀ 0 + r) = right (x₀ 1 - r)

/-- The canonical right-side limit of a common sequence of planar functions. -/
def squareLoopRightUniformLimit (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit (fun n => squareLoopRightRestriction (u n) x₀ r)

/-- The canonical top-side limit of a common sequence of planar functions. -/
def squareLoopTopUniformLimit (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit (fun n => squareLoopTopRestriction (u n) x₀ r)

/-- The canonical left-side limit of a common sequence of planar functions. -/
def squareLoopLeftUniformLimit (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit (fun n => squareLoopLeftRestriction (u n) x₀ r)

/-- The canonical bottom-side limit of a common sequence of planar functions. -/
def squareLoopBottomUniformLimit (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) : ℝ → ℝ :=
  uniformCauchySeqLimit (fun n => squareLoopBottomRestriction (u n) x₀ r)

private theorem uniformCauchySeqLimit_eq_of_forall_eq
    {F G : ℕ → ℝ → ℝ} {s t : ℝ} (h : ∀ n, F n s = G n t) :
    uniformCauchySeqLimit F s = uniformCauchySeqLimit G t := by
  unfold uniformCauchySeqLimit
  congr 1
  funext n
  exact h n

/-- The canonical right and top limits agree at their shared upper-right
corner.  The proof is pointwise equality of each common planar approximant
followed by equality of their `limUnder` limits. -/
theorem squareLoopRightUniformLimit_eq_top_at_corner
    (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) :
    squareLoopRightUniformLimit u x₀ r (x₀ 1 + r) =
      squareLoopTopUniformLimit u x₀ r (x₀ 0 + r) := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [squareLoopRightRestriction, squareLoopTopRestriction]
  congr 1

/-- The canonical top and left limits agree at their shared upper-left
corner. -/
theorem squareLoopTopUniformLimit_eq_left_at_corner
    (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) :
    squareLoopTopUniformLimit u x₀ r (x₀ 0 - r) =
      squareLoopLeftUniformLimit u x₀ r (x₀ 1 + r) := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [squareLoopTopRestriction, squareLoopLeftRestriction]
  congr 1

/-- The canonical left and bottom limits agree at their shared lower-left
corner. -/
theorem squareLoopLeftUniformLimit_eq_bottom_at_corner
    (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) :
    squareLoopLeftUniformLimit u x₀ r (x₀ 1 - r) =
      squareLoopBottomUniformLimit u x₀ r (x₀ 0 - r) := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [squareLoopLeftRestriction, squareLoopBottomRestriction]
  congr 1

/-- The canonical bottom and right limits agree at their shared lower-right
corner. -/
theorem squareLoopBottomUniformLimit_eq_right_at_corner
    (u : ℕ → Vec 2 → ℝ) (x₀ : Vec 2) (r : ℝ) :
    squareLoopBottomUniformLimit u x₀ r (x₀ 0 + r) =
      squareLoopRightUniformLimit u x₀ r (x₀ 1 - r) := by
  apply uniformCauchySeqLimit_eq_of_forall_eq
  intro n
  simp only [squareLoopBottomRestriction, squareLoopRightRestriction]
  congr 1

end

end PDE
