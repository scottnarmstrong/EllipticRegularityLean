module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Main
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.Basic
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Proof of `PDE.exists_poincare_adjustmean_constant` (Proposition 1.10)

Assembled in `PDE.PoincareAdjustMean`.
-/

@[expose] public section

namespace PDE.PoincareAdjustMeanProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) :
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
              (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.PoincareAdjustMean.exists_poincare_adjustmean_constant_full d hd

end PDE.PoincareAdjustMeanProof
