module

public import PDEFoundation.Monotonicity.Core.Bridge
public import PDEFoundation.Monotonicity.Core.BallDivergenceOneDim

/-!
# Chapter 2 frequency derivatives: dimension one

The unit sphere of `HilbertVec 1` is the two-point set `{±e}`, each point of mass one for
`Measure.toSphere` (`PDEFoundation.Monotonicity.Core.BallDivergenceOneDim`); its total mass is `2`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

/-- Total mass of the one-dimensional unit sphere. -/
theorem sphereArea_one : sphereArea 1 = 2 := by
  have hone := OneDim.integral_sphereMeasure_one (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at hone
  rw [sphereArea]
  rw [hone]
  norm_num

end PDE
