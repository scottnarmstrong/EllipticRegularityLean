module

public import EllipticRegularity.Ch4.GreenDecayDGNProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Measurable coefficients corollary (Corollary 4.36), `d ≥ 3`: with the De Giorgi
exponent `α ≥ exp(-C Λ^{(d+2)/4})`, decay rate `r^{2-α-d}` and constant `C Λ^{1/2 + d/4}`. -/
theorem greenDecayDGN (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₂ C : ℝ, 0 < C₂ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      Real.exp (-(C₂ * Λ ^ (((d : ℝ) + 2) / 4))) ≤ α ∧
      ∀ (R : ℝ), 10 ≤ R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Λ ^ ((1 : ℝ) / 2 + (d : ℝ) / 4) * r ^ (2 - α - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.GreenDecayDGNProof.result d hd

end PDE
