module

public import EllipticRegularity.DeGiorgi.MoserIter.LocalMax
public import EllipticRegularity.DeGiorgi.OneStep.Main
public import EllipticRegularity.DeGiorgi.Scaled.Bounded
public import EllipticRegularity.DeGiorgi.Glue.PositivePart
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Sobolev.H1.Basic

/-!
# Proof of `PDE.exists_moserLocalMax_constant` (Proposition 4.13)

-/

@[expose] public section

namespace PDE.MoserLocalMaxProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ p : ℝ, 1 < p →
        (essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) ^ p ≤
          ENNReal.ofReal (C * Λ ^ ((d : ℝ) / 2) * (p / (p - 1)) ^ (d : ℝ)) *
            (eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1))) ^ p :=
  PDE.DGNMMoser.exists_moserLocalMax_constant_full d hd (PDE.DGNMOneStep.moserOneStep d hd) (PDE.DGNMScaled.subsolutionBounded d hd) (PDE.DGNMGlue.positivePartSubsolution d)

end PDE.MoserLocalMaxProof
