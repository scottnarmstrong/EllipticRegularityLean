module

public import PDEFoundation.Analysis.Inequalities.GaussianPoincare.Final
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.gaussian_poincare` (Proposition 1.21)

Assembled from the Gaussian interpolation argument in
`PDE.GaussianPoincare`.
-/

@[expose] public section

namespace PDE.GaussianPoincareProof

open MeasureTheory

theorem result (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (ht : 0 < t) (u : Vec d → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    (∫ x, u x ^ 2 * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) -
        (∫ x, u x * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t)))) ^ 2 ≤
      2 * t * ∫ x, vecEuclideanNorm (classicalGradient u x) ^ 2 *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-vecNormSq x / (4 * t))) :=
  PDE.GaussianPoincare.gaussian_poincare_full d hd t ht u hu hc

end PDE.GaussianPoincareProof
