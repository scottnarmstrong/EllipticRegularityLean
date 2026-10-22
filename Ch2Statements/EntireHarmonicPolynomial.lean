module

public import PDEFoundation.Monotonicity.EntireHarmonicPolynomialProof

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

/-- An entire harmonic function of bounded frequency is a polynomial of degree at most `⌊N⌋` (Corollary 2.9, second claim). -/
theorem entire_harmonic_polynomial_of_frequency_bound (d : ℕ) (hd : 0 < d) (u : Vec d → ℝ)
    (hu : ContDiff ℝ 2 u) (hharm : ∀ x, euclideanCoordLaplacian u x = 0) (hu0 : u 0 = 0)
    (N : ℝ) (hN : ∀ r : ℝ, 0 < r → almgrenFrequency u r ≤ N) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ⌊N⌋₊ ∧ ∀ x, u x = MvPolynomial.eval x p := by exact PDE.EntireHarmonicPolynomialProof.result d hd u hu hharm hu0 N hN

end PDE
