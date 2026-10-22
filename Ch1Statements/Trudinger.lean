module

public import PDEFoundation.Sobolev.Inequalities.TrudingerProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Trudinger inequality (Proposition 1.18). -/
theorem exists_trudinger_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1pFunction (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal d),
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall (0 : Vec d) 1 |
            t < |u.toFun z - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun|}).toReal ≤
          (if (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal d)
                (volumeOn (euclideanBall (0 : Vec d) 1))).toReal = 0 then 0 else
            C * Real.exp (-(1 / C) * (t / (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal d) (volumeOn (euclideanBall (0 : Vec d) 1))).toReal) ^
                ((d : ℝ) / ((d : ℝ) - 1)))) := by exact PDE.TrudingerProof.result d hd

end PDE
