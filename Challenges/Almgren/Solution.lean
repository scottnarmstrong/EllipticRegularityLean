module

public import PDEFoundation.Monotonicity.AlmgrenMonotonicityProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- Almgren frequency monotonicity, with the equality case (Theorem 2.2).  For a harmonic `C²`
function `u` on the ball `B_R`, the frequency `r ↦ r ∫_{B_r} |∇u|² / ∫_{∂B_r} u²` is monotone on
`(0, R)`, and its derivative vanishes at a radius `r` exactly when `u` is a homogeneous polynomial
on `B_R`. -/
theorem almgren_monotonicity (d : ℕ) (hd : 0 < d) (R : ℝ) (hR : 0 < R)
    (u : Vec d → ℝ)
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    MonotoneOn (almgrenFrequency u) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R,
        deriv (almgrenFrequency u) r = 0 ↔
          ∃ (k : ℕ) (p : MvPolynomial (Fin d) ℝ), p.IsHomogeneous k ∧
            ∀ x ∈ euclideanBall (0 : Vec d) R, u x = MvPolynomial.eval x p :=
  PDE.AlmgrenMonotonicityProof.result d hd R hR u hu hharm

end PDE
