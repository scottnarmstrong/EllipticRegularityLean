module

public import PDEFoundation.Analysis.Inequalities.Trudinger.Main
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.exists_trudinger_constant` (Proposition 1.18)

Assembled in `PDE.Trudinger` from the convex Riesz bound and the maximal function.
-/

@[expose] public section

namespace PDE.TrudingerProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W1pFunction (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal d),
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ euclideanBall (0 : Vec d) 1 |
            t < |u.toFun z - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun|}).toReal ≤
          (if (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal d)
                (volumeOn (euclideanBall (0 : Vec d) 1))).toReal = 0 then 0 else
            C * Real.exp (-(1 / C) * (t / (eLpNorm (fun x => vecEuclideanNorm (u.grad x))
                (ENNReal.ofReal d) (volumeOn (euclideanBall (0 : Vec d) 1))).toReal) ^
                ((d : ℝ) / ((d : ℝ) - 1)))) :=
  PDE.Trudinger.exists_trudinger_constant_full d hd

end PDE.TrudingerProof
