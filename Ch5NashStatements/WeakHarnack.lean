module

public import EllipticRegularity.Parabolic.Nash.WeakHarnackProof

@[expose] public section

namespace PDE

open MeasureTheory Set

/-- Proposition 5.13 on `(-1,0] × B₁` (`λ = 1`): normalized `L^p` average, `p = q(d+2)/d`, over
`Q⁻ = (-3/4,-1/2) × B_{1/2}` is at most `C` times the essential infimum over `Q⁺ = (-1/4,0] × B_{1/2}`.
ENNReal-valued (`essInf` over a positive-measure set, `volume Q⁻ ∈ (0,∞)`), so no junk. -/
theorem parabWeakHarnack (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
        ((volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)))⁻¹ *
            ∫⁻ z in euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2),
              ENNReal.ofReal (u.toFun z) ^ (q * ((d : ℝ) + 2) / d)) ^ (1 / (q * ((d : ℝ) + 2) / d))
          ≤ ENNReal.ofReal C *
            essInf (fun z => ENNReal.ofReal (u.toFun z))
              (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)) := by exact PDE.Ch5NashWeakHarnackProof.result d hd Lam hLam q hq0 hq1

end PDE
