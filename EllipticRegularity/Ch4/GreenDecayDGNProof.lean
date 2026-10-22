module

public import EllipticRegularity.Ch4.GreenDecay.DecayDGNFull
public import PDEFoundation
public import EllipticRegularity.Green.GreenFunctionDef

/-!
# Proof of `PDE.greenDecayDGN` (Corollary 4.36)

-/

@[expose] public section

namespace PDE.GreenDecayDGNProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) :
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
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  PDE.Ch4GreenDecay.greenDecayDGN_full  d hd

end PDE.GreenDecayDGNProof
