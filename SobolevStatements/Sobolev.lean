module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Sobolev inequality for `1 ≤ p < d` on `ℝ^d` and for zero-boundary
functions on open sets, with the factor `γ_p = p (d - 1) / (d - p)`
(Proposition 1.5). -/
theorem exists_sobolev_constant
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p → p < d →
        (∀ u : W1pFunction (Set.univ : Set (Vec d)) (ENNReal.ofReal p),
          eLpNorm u.toFun (ENNReal.ofReal (sobolevConjugate d p)) volume ≤
            ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
              eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal p) volume) ∧
        (∀ (U : Set (Vec d)), IsOpen U →
          ∀ u : W1pFunction U (ENNReal.ofReal p),
          u.HasSupportedSmoothApproximation →
            eLpNorm u.toFun (ENNReal.ofReal (sobolevConjugate d p))
                (volumeOn U) ≤
              ENNReal.ofReal (C * (p * ((d : ℝ) - 1) / ((d : ℝ) - p))) *
                eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                  (ENNReal.ofReal p) (volumeOn U)) := by exact PDE.SobolevWholeSpaceProof.result d hd

end PDE
