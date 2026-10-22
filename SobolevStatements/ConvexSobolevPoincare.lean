module

public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Sobolev--Poincaré inequality on bounded convex domains, with
normalized `L^{p*}` and `L^p` norms on `V`, a constant depending only on the
dimension, the factor `γ_p = p (d - 1) / (d - p)`, and the diameter
(Theorem 1.9). -/
theorem exists_convexSobolevPoincare_constant
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
              euclideanFieldELpMeanNormOn V (ENNReal.ofReal p) u.grad := by exact PDE.ConvexSobolevPoincareProof.result d hd

end PDE
