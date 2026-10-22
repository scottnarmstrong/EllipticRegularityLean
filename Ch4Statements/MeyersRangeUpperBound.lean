module

public import EllipticRegularity.Ch4.MeyersRangeUpperBoundProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Consequence of Proposition 4.7 for the interior estimate of Theorem 4.4(i):
if for some `c > 0` and every `Λ > 1` the interior estimate holds for all `p ∈ [2, 2 + c/√Λ]`
with a finite constant `C` (allowed to depend on `d` and `Λ`), then `c ≤ 2`. -/
theorem meyers_range_upper_bound (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (h : ∀ Λ : ℝ, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ p : ℝ, 2 ≤ p → p ≤ 2 + c / Real.sqrt Λ →
        ∀ f : Vec d → Vec d,
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
                  (ENNReal.ofReal p) f)) :
    c ≤ 2 := by exact PDE.MeyersRangeUpperBoundProof.result d hd c hc h

end PDE
