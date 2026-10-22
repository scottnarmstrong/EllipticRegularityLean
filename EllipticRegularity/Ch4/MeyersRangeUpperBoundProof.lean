module

public import EllipticRegularity.Ch4.Meyers.RangeBound
public import PDEFoundation

/-!
# Proof of `PDE.meyers_range_upper_bound` (Proposition 4.7)

-/

@[expose] public section

namespace PDE.MeyersRangeUpperBoundProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
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
    c ≤ 2 :=
  PDE.Ch4Meyers.meyers_range_upper_bound_full  d hd c hc h

end PDE.MeyersRangeUpperBoundProof
