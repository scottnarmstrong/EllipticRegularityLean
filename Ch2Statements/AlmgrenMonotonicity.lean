module

public import PDEFoundation.Monotonicity.AlmgrenMonotonicityProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- Almgren frequency monotonicity, with the equality case (Theorem 2.2). -/
theorem almgren_monotonicity (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    MonotoneOn (almgrenFrequency u) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R,
        deriv (almgrenFrequency u) r = 0 ↔
          ∃ (k : ℕ) (p : MvPolynomial (Fin d) ℝ), p.IsHomogeneous k ∧
            ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p := by exact PDE.AlmgrenMonotonicityProof.result d hd R hR u hu hharm

end PDE
