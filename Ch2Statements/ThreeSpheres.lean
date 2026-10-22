module

public import PDEFoundation.Monotonicity.ThreeSpheresProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Three sphere theorem: `log ⨍_{∂B_{e^t}} u²` is convex in `t` (Corollary, three sphere theorem). -/
theorem three_spheres (d : ℕ) (hd : 0 < d) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) r₀))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) r₀, euclideanCoordLaplacian u x = 0) :
    ConvexOn ℝ (Set.Iio (Real.log r₀))
      (fun t : ℝ => Real.log (sphereMean (0 : Vec d) (Real.exp t) (fun x => u x ^ 2))) := by exact PDE.ThreeSpheresProof.result d hd r₀ hr₀ u hu hharm

end PDE
