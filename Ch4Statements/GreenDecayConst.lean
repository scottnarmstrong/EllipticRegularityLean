module

public import EllipticRegularity.Ch4.GreenDecayConstProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Constant coefficients corollary (Corollary 4.37): if `a = a₀` a.e. in `B_R`
with `a₀` elliptic, the decay rate is `r^{1-d}` with constant `C Λ^{(d+4)/4}`. -/
theorem greenDecayConst (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 10 ≤ R → ∀ (a : CoeffField d) (a₀ : Mat d),
      IsEllipticMatrix 1 Λ a₀ →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), a x = a₀) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Λ ^ (((d : ℝ) + 4) / 4) * r ^ (1 - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.GreenDecayConstProof.result d hd

end PDE
