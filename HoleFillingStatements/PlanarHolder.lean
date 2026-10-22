module

public import EllipticRegularity.Holder.PlanarHolderProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Hölder regularity in two dimensions with the sharp prefactor
`Λ ^ (1 / 2)` (Proposition 4.3). -/
theorem exists_planarHolder_constant :
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
              Real.sqrt (∫ x in euclideanBall (0 : Vec 2) 1, u.toFun x ^ 2) := by exact PDE.PlanarHolderProof.result

end PDE
