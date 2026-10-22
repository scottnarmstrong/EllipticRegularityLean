module

public import EllipticRegularity.Meyers.MeyersProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- The Meyers estimate with the range of exponents `2 + c / √Λ`
(Theorem 4.4): the interior estimate for `p ∈ [2, 2 + c/√Λ]` and the
Dirichlet estimate for `p ∈ [(2 + c/√Λ)', 2 + c/√Λ]`. -/
theorem exists_meyers_constants
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      (∀ (p : ℝ), 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
              (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
            ENNReal.ofReal C *
              (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
                  (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
                euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal p) f)) ∧
      (∀ (p : ℝ), (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p →
        p ≤ 2 + c / Real.sqrt Λ →
        ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
              (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
            ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
                (volumeOn (euclideanBall (0 : Vec d) 1))) := by exact PDE.MeyersProof.result d hd

end PDE
