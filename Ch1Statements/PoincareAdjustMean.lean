module

public import PDEFoundation.Sobolev.Inequalities.PoincareAdjustMeanProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Poincaré inequality with the mean over a subset (Proposition 1.10). -/
theorem exists_poincare_adjustmean_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ E : Set (Vec d), MeasurableSet E → E ⊆ euclideanBall (0 : Vec d) 1 →
        ENNReal.ofReal θ * volume (euclideanBall (0 : Vec d) 1) ≤ volume E →
        eLpNorm (fun x => u.toFun x - integralAverage E u.toFun) 2
            (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt (1 + |Real.log θ|)
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
        ENNReal.ofReal |integralAverage (euclideanBall (0 : Vec d) 1) u.toFun -
            integralAverage E u.toFun| ≤
          ENNReal.ofReal (C * (if d = 2 then Real.sqrt |Real.log θ|
              else θ ^ (((2 : ℝ) - d) / (2 * d)))) *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
              (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.PoincareAdjustMeanProof.result d hd

end PDE
