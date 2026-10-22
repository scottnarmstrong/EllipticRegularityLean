module

public import PDEFoundation.Sobolev.Inequalities.GaussianPoincareProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Gaussian Poincaré inequality (Proposition 1.21), with the heat kernel
`Φ(t,x) = (4πt)^{-d/2} exp(-|x|²/(4t))`. -/
theorem gaussian_poincare (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (ht : 0 < t) (u : Vec d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    (∫ x, u x ^ 2 * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) -
        (∫ x, u x * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) ^ 2 ≤
      2 * t * ∫ x, vecEuclideanNorm (classicalGradient u x) ^ 2 *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t))) := by exact PDE.GaussianPoincareProof.result d hd t ht u hu hc

end PDE
