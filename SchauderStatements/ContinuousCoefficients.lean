module

public import EllipticRegularity.Schauder.ContinuousCoefficientsProof

@[expose] public section

namespace PDE
open MeasureTheory Filter
open scoped ENNReal Topology

theorem exists_continuousCoefficientCalpha_constant
    {d : ℕ} (hd : 0 < d) {Λ : ℝ}
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ω : ℝ → ℝ) (hω0 : ω 0 = 0)
    (hωnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ ω t)
    (hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      ContinuousOn a (euclideanClosedBall (0 : Vec d) 1) →
      (∀ x ∈ euclideanClosedBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      (∀ x ∈ euclideanClosedBall (0 : Vec d) 1,
        ∀ y ∈ euclideanClosedBall (0 : Vec d) 1,
        IsMatrixPerturbationLE (ω (vecEuclideanNorm (x - y))) (a x) (a y)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ F : Vec d → Vec d,
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((d : ℝ) / (1 - α)))
        (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u.toFun α
        ((C / α) * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF / (1 - α))) := by exact PDE.SchauderContinuousProof.result hd hα0 hα1 ω hω0 hωnonneg hωlim

end PDE
