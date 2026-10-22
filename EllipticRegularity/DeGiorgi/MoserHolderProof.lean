module

public import EllipticRegularity.DeGiorgi.Assembly.MoserHolder
public import EllipticRegularity.DeGiorgi.Assembly.Harnack
public import EllipticRegularity.DeGiorgi.Assembly.WeakHarnack
public import EllipticRegularity.DeGiorgi.Assembly.AffineTransferProof
public import DGNMStatements.WeakHarnack0
public import DGNMStatements.Crossover
public import DGNMStatements.MoserLocalMax
public import DGNMStatements.DeGiorgiHolder
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Sobolev.H1.Basic

/-!
# Proof of `PDE.exists_moser_holder_constant` (Theorem 4.21)

-/

@[expose] public section

namespace PDE.MoserHolderProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, Real.exp (-(C * Real.sqrt Λ)) ≤ α ∧ α ≤ 1 ∧
      ∀ (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
      ∀ p : ℝ, 1 < p →
        ∃ (v : Vec d → ℝ) (M₀ M₁ : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M₀ ∧ 0 ≤ M₁ ∧ (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), |v x| ≤ M₀) ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M₁ ∧
          ENNReal.ofReal (M₀ + M₁) ≤
            ENNReal.ofReal (C * Λ ^ ((d : ℝ) / (2 * p)) * (p / (p - 1)) ^ ((d : ℝ) / p)) *
              eLpNorm u.toFun (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.DGNMAssembly.exists_moser_holder_constant_full d hd (PDE.DGNMAssembly.exists_harnack_constant_full d hd (PDE.DGNMAssembly.exists_weakHarnack_constant_full d hd (PDE.exists_weakHarnack0_constant d hd) (PDE.exists_crossover_constants d (by omega)) (PDE.DGNMAssembly.superAffineTransfer d)) (PDE.exists_moserLocalMax_constant d hd) (PDE.exists_deGiorgi_holder_constant d hd) (PDE.DGNMAssembly.solAffineTransfer d)) (PDE.exists_moserLocalMax_constant d hd) (PDE.exists_deGiorgi_holder_constant d hd) (PDE.DGNMAssembly.solAffineTransfer d)

end PDE.MoserHolderProof
