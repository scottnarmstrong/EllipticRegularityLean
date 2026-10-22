module

public import EllipticRegularity.Holder.PlanarHolderAssembly
public import PDEFoundation.PDE.CoefficientModification

/-!
# Proof of `PDE.exists_planarHolder_constant` (Proposition 4.3)

The sharp two-dimensional Hölder estimate for coefficients whose entries are
a.e. measurable and which are elliptic at every point of the unit disc,
obtained from the assembly theorem for a measurable elliptic representative.
-/

@[expose] public section

namespace PDE.PlanarHolderProof

open MeasureTheory

theorem result :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec 2) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec 2) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u
          (0 : Vec 2 → ℝ) (0 : Vec 2 → Vec 2) →
      ∃ v : Vec 2 → ℝ,
        (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 2) (1 / 2)), v x = u.toFun x) ∧
        ∃ M H : ℝ,
          (∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2), |v x| ≤ M) ∧
          (∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
            ∀ y ∈ euclideanBall (0 : Vec 2) (1 / 2),
              |v x - v y| ≤
                H * vecEuclideanNorm (x - y) ^ ((C * Λ) ^ (-(1 / 2 : ℝ)))) ∧
          M + H ≤
            C * Real.sqrt Λ *
              Real.sqrt (∫ x in euclideanBall (0 : Vec 2) 1, u.toFun x ^ 2) := by
  refine ⟨planarHolderAssemblyConstant, by norm_num [planarHolderAssemblyConstant], ?_⟩
  intro Λ a ha hEll u hsol
  obtain ⟨b, hbEll, -, hbsol⟩ :=
    exists_isEllipticFieldOn_and_weakSolutionOn_coeffAEEqOn
      (measurableSet_euclideanBall (0 : Vec 2) 1) ha hEll hsol
  exact planarHolder_of_isEllipticFieldOn hbEll hbsol

end PDE.PlanarHolderProof
