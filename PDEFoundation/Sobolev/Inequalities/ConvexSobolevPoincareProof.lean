module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareAffine

/-!
# Proof of `PDE.exists_convexSobolevPoincare_constant` (Theorem 1.9)

The Sobolev--Poincaré inequality on bounded convex domains with constant
`C(d) γ_p diam V`, assembled from the normalized estimate and the affine
normalization of the domain.
-/

@[expose] public section

namespace PDE.ConvexSobolevPoincareProof

open MeasureTheory

theorem result
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p → p < d →
      ∀ (V : Set (Vec d)) (D : ℝ),
        IsOpenBoundedConvexDomain V → V.Nonempty →
        HasEuclideanDiameterLE V D →
        ∀ u : W1pFunction V (ENNReal.ofReal p),
          eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d p))
              (fun x => u.toFun x - integralAverage V u.toFun) ≤
            ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p)) * D) *
              euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad :=
  exists_convexSobolevPoincare_of_normalized hd

end PDE.ConvexSobolevPoincareProof
