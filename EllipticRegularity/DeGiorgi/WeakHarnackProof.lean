module

public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnack
public import EllipticRegularity.DeGiorgi.Assembly.AffineTransferProof
public import DGNMStatements.WeakHarnack0
public import DGNMStatements.Crossover
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Sobolev.H1.Basic

/-!
# Proof of `PDE.exists_weakHarnack_constant` (Proposition 4.17)

-/

@[expose] public section

namespace PDE.WeakHarnackProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
      ∀ q : ℝ, 0 < q → q < 1 →
        eLpNorm u.toFun (ENNReal.ofReal (q * d / (d - 2))) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) ≤
          ENNReal.ofReal ((C / (1 - q) ^ C) ^ Real.sqrt Λ) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 4))) :=
  PDE.DGNMAssembly.exists_weakHarnack_constant_full d hd (PDE.exists_weakHarnack0_constant d hd) (PDE.exists_crossover_constants d (by omega)) (PDE.DGNMAssembly.superAffineTransfer d)

end PDE.WeakHarnackProof
