module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Geometry.SquarePoint

/-!
# Oriented loops around centered axis squares

The square convention agrees with the native points and centered axis cubes
used by the good-radius Fubini argument.  The loop starts at the lower-right
corner, travels counterclockwise, and has four affine sides of Euclidean speed
one.
-/

@[expose] public section

namespace PDE

open Set

noncomputable section

/-- The closed boundary of the centered native axis square. -/
def centeredAxisSquareBoundary (x₀ : Vec 2) (r : ℝ) : Set (Vec 2) :=
  closedCenteredAxisCube x₀ r \ centeredAxisCube x₀ r

/-- The right side, oriented from bottom to top. -/
def squareLoopRightSide (x₀ : Vec 2) (r t : ℝ) : Vec 2 :=
  squarePoint (x₀ 0 + r) t

/-- The top side with its horizontal coordinate as parameter.  The loop below
uses this side with decreasing parameter, hence traverses it from right to left. -/
def squareLoopTopSide (x₀ : Vec 2) (r t : ℝ) : Vec 2 :=
  squarePoint t (x₀ 1 + r)

/-- The left side with its vertical coordinate as parameter.  The loop below
uses this side with decreasing parameter, hence traverses it from top to bottom. -/
def squareLoopLeftSide (x₀ : Vec 2) (r t : ℝ) : Vec 2 :=
  squarePoint (x₀ 0 - r) t

/-- The bottom side, oriented from left to right. -/
def squareLoopBottomSide (x₀ : Vec 2) (r t : ℝ) : Vec 2 :=
  squarePoint t (x₀ 1 - r)

/-- The Euclidean unit direction of the loop on its right side. -/
def squareLoopRightDirection : Vec 2 := basisVec (1 : Fin 2)

/-- The Euclidean unit direction of the loop on its top side. -/
def squareLoopTopDirection : Vec 2 := -basisVec (0 : Fin 2)

/-- The Euclidean unit direction of the loop on its left side. -/
def squareLoopLeftDirection : Vec 2 := -basisVec (1 : Fin 2)

/-- The Euclidean unit direction of the loop on its bottom side. -/
def squareLoopBottomDirection : Vec 2 := basisVec (0 : Fin 2)

/-- A counterclockwise piecewise-affine traversal of the square of half-side
`r`, parametrized on `[0, 8r]` when `r > 0`. -/
def squareLoop (x₀ : Vec 2) (r t : ℝ) : Vec 2 :=
  if t ≤ 2 * r then
    squareLoopRightSide x₀ r (x₀ 1 - r + t)
  else if t ≤ 4 * r then
    squareLoopTopSide x₀ r (x₀ 0 + 3 * r - t)
  else if t ≤ 6 * r then
    squareLoopLeftSide x₀ r (x₀ 1 + 5 * r - t)
  else
    squareLoopBottomSide x₀ r (x₀ 0 + t - 7 * r)

/-- The polygonal length of the four oriented sides of the square loop. -/
def squareLoopLength (x₀ : Vec 2) (r : ℝ) : ℝ :=
  vecEuclideanNorm
      (squareLoopRightSide x₀ r (x₀ 1 + r) -
        squareLoopRightSide x₀ r (x₀ 1 - r)) +
    vecEuclideanNorm
      (squareLoopTopSide x₀ r (x₀ 0 - r) -
        squareLoopTopSide x₀ r (x₀ 0 + r)) +
    vecEuclideanNorm
      (squareLoopLeftSide x₀ r (x₀ 1 - r) -
        squareLoopLeftSide x₀ r (x₀ 1 + r)) +
    vecEuclideanNorm
      (squareLoopBottomSide x₀ r (x₀ 0 + r) -
        squareLoopBottomSide x₀ r (x₀ 0 - r))

@[simp] theorem squareLoopRightSide_zero (x₀ : Vec 2) (r t : ℝ) :
    squareLoopRightSide x₀ r t 0 = x₀ 0 + r := by
  simp [squareLoopRightSide]

@[simp] theorem squareLoopRightSide_one (x₀ : Vec 2) (r t : ℝ) :
    squareLoopRightSide x₀ r t 1 = t := by
  simp [squareLoopRightSide]

@[simp] theorem squareLoopTopSide_zero (x₀ : Vec 2) (r t : ℝ) :
    squareLoopTopSide x₀ r t 0 = t := by
  simp [squareLoopTopSide]

@[simp] theorem squareLoopTopSide_one (x₀ : Vec 2) (r t : ℝ) :
    squareLoopTopSide x₀ r t 1 = x₀ 1 + r := by
  simp [squareLoopTopSide]

@[simp] theorem squareLoopLeftSide_zero (x₀ : Vec 2) (r t : ℝ) :
    squareLoopLeftSide x₀ r t 0 = x₀ 0 - r := by
  simp [squareLoopLeftSide]

@[simp] theorem squareLoopLeftSide_one (x₀ : Vec 2) (r t : ℝ) :
    squareLoopLeftSide x₀ r t 1 = t := by
  simp [squareLoopLeftSide]

@[simp] theorem squareLoopBottomSide_zero (x₀ : Vec 2) (r t : ℝ) :
    squareLoopBottomSide x₀ r t 0 = t := by
  simp [squareLoopBottomSide]

@[simp] theorem squareLoopBottomSide_one (x₀ : Vec 2) (r t : ℝ) :
    squareLoopBottomSide x₀ r t 1 = x₀ 1 - r := by
  simp [squareLoopBottomSide]

theorem squareLoop_eq_rightSide {x₀ : Vec 2} {r t : ℝ} (ht : t ≤ 2 * r) :
    squareLoop x₀ r t = squareLoopRightSide x₀ r (x₀ 1 - r + t) := by
  simp [squareLoop, ht]

theorem squareLoop_eq_topSide {x₀ : Vec 2} {r t : ℝ}
    (hleft : 2 * r < t) (hright : t ≤ 4 * r) :
    squareLoop x₀ r t = squareLoopTopSide x₀ r (x₀ 0 + 3 * r - t) := by
  simp [squareLoop, hleft.not_ge, hright]

theorem squareLoop_eq_leftSide {x₀ : Vec 2} {r t : ℝ}
    (hleft : 4 * r < t) (hright : t ≤ 6 * r) :
    squareLoop x₀ r t = squareLoopLeftSide x₀ r (x₀ 1 + 5 * r - t) := by
  have htwo : ¬t ≤ 2 * r := by linarith
  simp [squareLoop, htwo, hleft.not_ge, hright]

theorem squareLoop_eq_bottomSide {x₀ : Vec 2} {r t : ℝ}
    (hr : 0 ≤ r) (hleft : 6 * r < t) :
    squareLoop x₀ r t = squareLoopBottomSide x₀ r (x₀ 0 + t - 7 * r) := by
  have htwo : ¬t ≤ 2 * r := by linarith
  have hfour : ¬t ≤ 4 * r := by linarith
  have hsix : ¬t ≤ 6 * r := hleft.not_ge
  simp [squareLoop, htwo, hfour, hsix]

theorem squareLoopRightSide_mem_boundary {x₀ : Vec 2} {r t : ℝ}
    (hr : 0 ≤ r) (ht : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r)) :
    squareLoopRightSide x₀ r t ∈ centeredAxisSquareBoundary x₀ r := by
  change squareLoopRightSide x₀ r t ∈ closedCenteredAxisCube x₀ r ∧
    squareLoopRightSide x₀ r t ∉ centeredAxisCube x₀ r
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - r ≤ x₀ 0 + r ∧ x₀ 0 + r ≤ x₀ 0 + r
      constructor <;> linarith
    · change x₀ 1 - r ≤ t ∧ t ≤ x₀ 1 + r
      exact ht
  · intro h
    have hright := h 0 (mem_univ 0)
    change x₀ 0 - r < x₀ 0 + r ∧ x₀ 0 + r < x₀ 0 + r at hright
    exact (lt_irrefl _ hright.2)

theorem squareLoopTopSide_mem_boundary {x₀ : Vec 2} {r t : ℝ}
    (hr : 0 ≤ r) (ht : t ∈ Icc (x₀ 0 - r) (x₀ 0 + r)) :
    squareLoopTopSide x₀ r t ∈ centeredAxisSquareBoundary x₀ r := by
  change squareLoopTopSide x₀ r t ∈ closedCenteredAxisCube x₀ r ∧
    squareLoopTopSide x₀ r t ∉ centeredAxisCube x₀ r
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - r ≤ t ∧ t ≤ x₀ 0 + r
      exact ht
    · change x₀ 1 - r ≤ x₀ 1 + r ∧ x₀ 1 + r ≤ x₀ 1 + r
      constructor <;> linarith
  · intro h
    have htop := h 1 (mem_univ 1)
    change x₀ 1 - r < x₀ 1 + r ∧ x₀ 1 + r < x₀ 1 + r at htop
    exact (lt_irrefl _ htop.2)

theorem squareLoopLeftSide_mem_boundary {x₀ : Vec 2} {r t : ℝ}
    (hr : 0 ≤ r) (ht : t ∈ Icc (x₀ 1 - r) (x₀ 1 + r)) :
    squareLoopLeftSide x₀ r t ∈ centeredAxisSquareBoundary x₀ r := by
  change squareLoopLeftSide x₀ r t ∈ closedCenteredAxisCube x₀ r ∧
    squareLoopLeftSide x₀ r t ∉ centeredAxisCube x₀ r
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - r ≤ x₀ 0 - r ∧ x₀ 0 - r ≤ x₀ 0 + r
      constructor <;> linarith
    · change x₀ 1 - r ≤ t ∧ t ≤ x₀ 1 + r
      exact ht
  · intro h
    have hleft := h 0 (mem_univ 0)
    change x₀ 0 - r < x₀ 0 - r ∧ x₀ 0 - r < x₀ 0 + r at hleft
    exact (lt_irrefl _ hleft.1)

theorem squareLoopBottomSide_mem_boundary {x₀ : Vec 2} {r t : ℝ}
    (hr : 0 ≤ r) (ht : t ∈ Icc (x₀ 0 - r) (x₀ 0 + r)) :
    squareLoopBottomSide x₀ r t ∈ centeredAxisSquareBoundary x₀ r := by
  change squareLoopBottomSide x₀ r t ∈ closedCenteredAxisCube x₀ r ∧
    squareLoopBottomSide x₀ r t ∉ centeredAxisCube x₀ r
  constructor
  · intro i _
    fin_cases i
    · change x₀ 0 - r ≤ t ∧ t ≤ x₀ 0 + r
      exact ht
    · change x₀ 1 - r ≤ x₀ 1 - r ∧ x₀ 1 - r ≤ x₀ 1 + r
      constructor <;> linarith
  · intro h
    have hbottom := h 1 (mem_univ 1)
    change x₀ 1 - r < x₀ 1 - r ∧ x₀ 1 - r < x₀ 1 + r at hbottom
    exact (lt_irrefl _ hbottom.1)

theorem squareLoopRightSide_coordinateIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopRightSide x₀ r (t + s) - squareLoopRightSide x₀ r t =
      s • basisVec (1 : Fin 2) := by
  funext i
  fin_cases i
  · simp [squareLoopRightSide, basisVec]
  · simp [squareLoopRightSide, basisVec]

theorem squareLoopTopSide_coordinateIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopTopSide x₀ r (t + s) - squareLoopTopSide x₀ r t =
      s • basisVec (0 : Fin 2) := by
  funext i
  fin_cases i
  · simp [squareLoopTopSide, basisVec]
  · simp [squareLoopTopSide, basisVec]

theorem squareLoopLeftSide_coordinateIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopLeftSide x₀ r (t + s) - squareLoopLeftSide x₀ r t =
      s • basisVec (1 : Fin 2) := by
  funext i
  fin_cases i
  · simp [squareLoopLeftSide, basisVec]
  · simp [squareLoopLeftSide, basisVec]

theorem squareLoopBottomSide_coordinateIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopBottomSide x₀ r (t + s) - squareLoopBottomSide x₀ r t =
      s • basisVec (0 : Fin 2) := by
  funext i
  fin_cases i
  · simp [squareLoopBottomSide, basisVec]
  · simp [squareLoopBottomSide, basisVec]

theorem squareLoopRightSide_timeIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopRightSide x₀ r (t + s) - squareLoopRightSide x₀ r t =
      s • squareLoopRightDirection := by
  simpa only [squareLoopRightDirection] using squareLoopRightSide_coordinateIncrement x₀ r s t

theorem squareLoopTopSide_timeIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopTopSide x₀ r (t - s) - squareLoopTopSide x₀ r t =
      s • squareLoopTopDirection := by
  funext i
  fin_cases i <;> simp [squareLoopTopSide, squareLoopTopDirection, basisVec]

theorem squareLoopLeftSide_timeIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopLeftSide x₀ r (t - s) - squareLoopLeftSide x₀ r t =
      s • squareLoopLeftDirection := by
  funext i
  fin_cases i <;> simp [squareLoopLeftSide, squareLoopLeftDirection, basisVec]

theorem squareLoopBottomSide_timeIncrement (x₀ : Vec 2) (r s t : ℝ) :
    squareLoopBottomSide x₀ r (t + s) - squareLoopBottomSide x₀ r t =
      s • squareLoopBottomDirection := by
  simpa only [squareLoopBottomDirection] using squareLoopBottomSide_coordinateIncrement x₀ r s t

theorem vecEuclideanNorm_squareLoopRightDirection :
    vecEuclideanNorm squareLoopRightDirection = 1 := by
  rw [squareLoopRightDirection, vecEuclideanNorm_basisVec]

theorem vecEuclideanNorm_squareLoopTopDirection :
    vecEuclideanNorm squareLoopTopDirection = 1 := by
  rw [squareLoopTopDirection, vecEuclideanNorm_neg, vecEuclideanNorm_basisVec]

theorem vecEuclideanNorm_squareLoopLeftDirection :
    vecEuclideanNorm squareLoopLeftDirection = 1 := by
  rw [squareLoopLeftDirection, vecEuclideanNorm_neg, vecEuclideanNorm_basisVec]

theorem vecEuclideanNorm_squareLoopBottomDirection :
    vecEuclideanNorm squareLoopBottomDirection = 1 := by
  rw [squareLoopBottomDirection, vecEuclideanNorm_basisVec]

theorem squareLoop_zero {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoop x₀ r 0 = squarePoint (x₀ 0 + r) (x₀ 1 - r) := by
  rw [squareLoop_eq_rightSide (by linarith)]
  simp [squareLoopRightSide]

theorem squareLoop_two_mul {x₀ : Vec 2} {r : ℝ} :
    squareLoop x₀ r (2 * r) = squarePoint (x₀ 0 + r) (x₀ 1 + r) := by
  rw [squareLoop_eq_rightSide le_rfl]
  simp [squareLoopRightSide]
  ring_nf

theorem squareLoop_four_mul {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoop x₀ r (4 * r) = squarePoint (x₀ 0 - r) (x₀ 1 + r) := by
  rw [squareLoop_eq_topSide (by linarith) (by linarith)]
  simp [squareLoopTopSide]
  ring_nf

theorem squareLoop_six_mul {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoop x₀ r (6 * r) = squarePoint (x₀ 0 - r) (x₀ 1 - r) := by
  rw [squareLoop_eq_leftSide (by linarith) le_rfl]
  simp [squareLoopLeftSide]
  ring_nf

theorem squareLoop_eight_mul {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoop x₀ r (8 * r) = squarePoint (x₀ 0 + r) (x₀ 1 - r) := by
  rw [squareLoop_eq_bottomSide hr.le (by linarith)]
  simp [squareLoopBottomSide]
  ring_nf

theorem squareLoop_closed {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoop x₀ r (8 * r) = squareLoop x₀ r 0 := by
  rw [squareLoop_eight_mul hr, squareLoop_zero hr]

theorem squareLoop_length_eq_eight_mul {x₀ : Vec 2} {r : ℝ} (hr : 0 < r) :
    squareLoopLength x₀ r = 8 * r := by
  have hright :
      squareLoopRightSide x₀ r (x₀ 1 + r) - squareLoopRightSide x₀ r (x₀ 1 - r) =
        (2 * r) • basisVec (1 : Fin 2) := by
    convert squareLoopRightSide_coordinateIncrement x₀ r (2 * r) (x₀ 1 - r) using 1
    all_goals ring_nf
  have htop :
      squareLoopTopSide x₀ r (x₀ 0 - r) - squareLoopTopSide x₀ r (x₀ 0 + r) =
        (-2 * r) • basisVec (0 : Fin 2) := by
    convert squareLoopTopSide_coordinateIncrement x₀ r (-2 * r) (x₀ 0 + r) using 1
    all_goals ring_nf
  have hleft :
      squareLoopLeftSide x₀ r (x₀ 1 - r) - squareLoopLeftSide x₀ r (x₀ 1 + r) =
        (-2 * r) • basisVec (1 : Fin 2) := by
    convert squareLoopLeftSide_coordinateIncrement x₀ r (-2 * r) (x₀ 1 + r) using 1
    all_goals ring_nf
  have hbottom :
      squareLoopBottomSide x₀ r (x₀ 0 + r) - squareLoopBottomSide x₀ r (x₀ 0 - r) =
        (2 * r) • basisVec (0 : Fin 2) := by
    convert squareLoopBottomSide_coordinateIncrement x₀ r (2 * r) (x₀ 0 - r) using 1
    all_goals ring_nf
  rw [squareLoopLength, hright, htop, hleft, hbottom]
  simp only [vecEuclideanNorm_smul, vecEuclideanNorm_basisVec,
    abs_of_pos (by linarith : 0 < 2 * r),
    abs_of_neg (by linarith : -2 * r < 0)]
  ring

end

end PDE
