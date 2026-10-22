module

public import PDEFoundation.Monotonicity.MonoSqBallsProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Growth of `⨍_{B_r} u²` for a nonconstant harmonic function vanishing at the origin (Lemma 2.8). -/
theorem mono_sq_balls (d : ℕ) (hd : 0 < d) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) r₀))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) r₀, euclideanCoordLaplacian u x = 0)
    (hnc : ¬ ∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) r₀, u x = c)
    (hu0 : u 0 = 0) :
    ∀ r ∈ Set.Ioo 0 r₀,
      2 / r * integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤
        deriv (fun s : ℝ => integralAverage (euclideanBall (0 : Vec d) s) (fun x => u x ^ 2)) r := by exact PDE.MonoSqBallsProof.result d hd r₀ hr₀ u hu hharm hnc hu0

end PDE
