module

public import EllipticRegularity.DeGiorgi.LogPackage.Crossover
public import EllipticRegularity.DeGiorgi.LogEnergy.Final
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Sobolev.H1.Basic

/-!
# Proof of `PDE.exists_crossover_constants` (Proposition 4.16)

-/

@[expose] public section

namespace PDE.CrossoverProof

open MeasureTheory

theorem result (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 2 ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (c * Λ ^ (-(1 : ℝ) / 2))) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (-(c * Λ ^ (-(1 : ℝ) / 2)))) ≤ ENNReal.ofReal C :=
  PDE.DGNMLog.exists_crossover_constants_full d hd (PDE.DGNMLogEnergy.logEnergy d)

end PDE.CrossoverProof
