module

public import EllipticRegularity.Energy.HoleFillingProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The hole-filling estimate in dimensions `d ≥ 2` (Lemma 4.2). -/
theorem exists_holeFilling_constant
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
          (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        Real.sqrt (∫ x in euclideanBall (0 : Vec d) r, vecNormSq (u.grad x)) ≤
          C * Real.sqrt Λ * r ^ ((C * Λ) ^ (-(1 / 2 : ℝ))) *
            Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, u.toFun x ^ 2) := by exact PDE.HoleFillingProof.result d hd

end PDE
