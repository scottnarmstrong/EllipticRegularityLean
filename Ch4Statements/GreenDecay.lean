module

public import EllipticRegularity.Ch4.GreenDecayProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Decay lemma (Lemma 4.35): an oscillation decay hypothesis for `aᵗ`-harmonic
functions in `B_ρ`, `ρ ∈ [4,R]`, gives decay of `u - (u)_{A_r}` in `L̲²(A_r)`, `r ∈ [10,R]`, for
the `H¹₀(B_R)` solution of `-div (a ∇ u) = div (f 1_{B_1})`. -/
theorem greenDecay (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 10 ≤ R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (β Cs : ℝ), 0 < β → β ≤ 1 → 0 ≤ Cs →
      (∀ ρ : ℝ, 4 ≤ ρ → ρ ≤ R → ∀ w : H1Function (euclideanBall (0 : Vec d) ρ),
        IsWeakDivergenceFormSolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) ρ) w
          (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
        ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
          m ≤ w.toFun x ∧
          ENNReal.ofReal (w.toFun x - m) ≤
            ENNReal.ofReal (Cs * ρ ^ (-β)) *
              eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
                (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun)) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.GreenDecayProof.result d hd

end PDE
