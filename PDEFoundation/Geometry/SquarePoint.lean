module

public import PDEFoundation.Ambient.Basic

/-!
# Native points in two coordinates

This tiny geometry module supplies the standard constructor for a point in
the project's native two-dimensional vector space.  Keeping it below both
square geometry and square-boundary measure theory avoids a dependency from
geometry back into the measure layer.
-/

@[expose] public section

namespace PDE

/-- The native point with first coordinate `s` and second coordinate `t`. -/
def squarePoint (s t : ℝ) : Vec 2 :=
  fun i => if i = (0 : Fin 2) then s else t

@[simp]
theorem squarePoint_zero (s t : ℝ) :
    squarePoint s t 0 = s := by
  simp [squarePoint]

@[simp]
theorem squarePoint_one (s t : ℝ) :
    squarePoint s t 1 = t := by
  simp [squarePoint]

end PDE
