module

public import EllipticRegularity.Ch4.Meyers.RangeBoundDirichlet
public import PDEFoundation

/-!
# Proof of `PDE.meyers_range_upper_bound_dirichlet` (Proposition 4.7)

-/

@[expose] public section

namespace PDE.MeyersRangeUpperBoundDirichletProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (h : ∀ Λ : ℝ, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ p : ℝ, (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p →
        p ≤ 2 + c / Real.sqrt Λ →
        ∀ f : Vec d → Vec d,
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
                (volumeOn (euclideanBall (0 : Vec d) 1))) :
    c ≤ 2 :=
  PDE.Ch4Meyers.meyers_range_upper_bound_dirichlet_full  d hd c hc h

end PDE.MeyersRangeUpperBoundDirichletProof
