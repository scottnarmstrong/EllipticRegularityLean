module

public import EllipticRegularity.DeGiorgi.CrossoverProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The crossover estimate (Proposition 4.16). -/
theorem exists_crossover_constants (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 2 ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSuperharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (c * Λ ^ (-(1 : ℝ) / 2))) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 1
            (fun x => u.toFun x ^ (-(c * Λ ^ (-(1 : ℝ) / 2)))) ≤ ENNReal.ofReal C := by exact PDE.CrossoverProof.result d hd

end PDE
