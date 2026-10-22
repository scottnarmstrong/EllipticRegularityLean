module

public import EllipticRegularity.Ch4.GreenDecay.DecayConstFull
public import PDEFoundation
public import EllipticRegularity.Green.GreenFunctionDef

/-!
# Proof of `PDE.greenDecayConst` (Corollary 4.37)

-/

@[expose] public section

namespace PDE.GreenDecayConstProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) :
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
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.Ch4GreenDecay.greenDecayConst_full  d hd

end PDE.GreenDecayConstProof
