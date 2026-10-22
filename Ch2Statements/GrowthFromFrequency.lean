module

public import PDEFoundation.Monotonicity.GrowthFromFrequencyProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Two-sided growth estimate from the frequency (Corollary 2.9, first claim). -/
theorem growth_from_frequency (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hu0 : u 0 = 0) :
    ∀ s r : ℝ, 0 < s → s < r → r < R →
      (s / r) ^ (2 * almgrenFrequency u r) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) ≤
          sphereMean (0 : Vec d) s (fun x => u x ^ 2) ∧
        sphereMean (0 : Vec d) s (fun x => u x ^ 2) ≤
          (s / r) ^ (2 * almgrenFrequency u s) * sphereMean (0 : Vec d) r (fun x => u x ^ 2) := by exact PDE.GrowthFromFrequencyProof.result d hd R hR u hu hharm hu0

end PDE
