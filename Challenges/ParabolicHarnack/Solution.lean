module

public import EllipticRegularity.Parabolic.Nash.LocalHarnackProof

@[expose] public section

open scoped BigOperators ENNReal

namespace PDE

open MeasureTheory Set

/-- The parabolic Harnack inequality (Corollary 5.14, ellipticity constants `1 ≤ Λ`).  For `d > 0` and `Λ ≥ 1`
there is `H ≥ 2` such that for every parabolic coefficient field `a` with constants `(1, Λ)` on the
space-time cylinder `B_{√(2θ)}((z+z')/2) × (τ - 3θ/2, τ + 5θ/4]`, `|z - z'|² ≤ θ/4`, and every nonnegative
weak solution `u` there, `ess sup_{B_{√θ/4}(z)} u(·, τ) ≤ H · ess inf_{B_{√θ/4}(z')} u(·, τ + θ)`
(essential supremum and infimum valued in `[0, ∞]`). -/
theorem parabLocalHarnack (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : ParCoeffField d) (τ θ : ℝ), 0 < θ → ∀ z z' : Vec d,
      euclideanSqDist z z' ≤ θ / 4 →
      IsParabolicCoeff 1 Lam a
        (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : ParH1Function (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
      IsParabolicWeakSolution a (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) u →
      (∀ᵐ w ∂(volume.restrict (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
        Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w) →
        essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
            (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
          ENNReal.ofReal H *
            essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
              (volume.restrict (euclideanBall z' (Real.sqrt θ / 4))) :=
  PDE.Ch5NashLocalHarnackProof.result d hd Lam hLam

end PDE
