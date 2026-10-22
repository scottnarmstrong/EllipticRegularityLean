module

public import EllipticRegularity.Parabolic.WeakHarnack.Assembly
public import EllipticRegularity.Parabolic.WeakHarnack.PowerStepFinal
public import EllipticRegularity.Parabolic.WeakHarnack.PowerStepFinite
public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateFinal

/-! # Proof of `PDE.parabWeakHarnack` (Proposition 5.13) -/

@[expose] public section

namespace PDE.Ch5NashWeakHarnackProof

open MeasureTheory Set PDE.Parabolic.WeakHarnack

/-- The parabolic weak Harnack inequality, assembled from the positive and negative power steps,
the finiteness of the `L^{qχ}` norm on the outer cylinder, and the logarithmic estimate. -/
theorem result (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) (q : ℝ)
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
              (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)) :=
  weakHarnack_of_steps d hd Lam hLam q hq0 hq1
    (parabPowerStepPos d hd Lam hLam q hq0 hq1)
    (parabPowerStepPosFinite d hd Lam hLam q hq0 hq1)
    (parabPowerStepNeg d hd Lam hLam)
    (parabPowerStepNegInner d hd Lam hLam)
    (log_tail_supersolution_H3 d Lam (by linarith))

end PDE.Ch5NashWeakHarnackProof
