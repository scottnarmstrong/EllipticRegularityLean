module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceDensity
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceLimit

/-!
# Sobolev inequality on the whole space and for zero-boundary functions

Proposition 1.5: for `1 ≤ p < d` the inequality
`‖u‖_{p*} ≤ C(d) · (p (d - 1) / (d - p)) · ‖∇u‖_p` holds for `u ∈ W^{1,p}(ℝ^d)` and
for `u ∈ W^{1,p}(U)` admitting a supported smooth approximation.  The constant
`C(d) = 1 + d · C₁(d)` depends only on the dimension; the exponent enters only
through the explicit factor `γ_p = p (d - 1) / (d - p)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

/-- Proposition 1.5: the Sobolev inequality for `1 ≤ p < d` on `ℝ^d` and
for zero-boundary functions on open sets, with the factor
`γ_p = p (d - 1) / (d - p)`. -/
theorem sobolev_inequality_wholeSpace_and_zeroBoundary
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
                  (ENNReal.ofReal p) (volumeOn U)) := by
  refine ⟨sobolevWholeSpaceConstant d, sobolevWholeSpaceConstant_pos d, fun p hp hpd => ⟨?_, ?_⟩⟩
  · intro u
    have hone : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
    obtain ⟨happrox⟩ := W1pFunction.hasSupportedSmoothApproximation_univ
      hone ENNReal.ofReal_ne_top u
    have := eLpNorm_sobolevConjugate_le_of_supportedSmoothApproximation hd hp hpd u happrox
    simpa only [volumeOn, Measure.restrict_univ] using this
  · intro U _ u happrox
    obtain ⟨happrox⟩ := happrox
    exact eLpNorm_sobolevConjugate_le_of_supportedSmoothApproximation hd hp hpd u happrox

end PDE
