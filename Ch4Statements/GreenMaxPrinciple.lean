module

public import EllipticRegularity.Ch4.GreenMaxPrincipleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Weak maximum principle (Lemma 4.34): a nonnegative weak supersolution in
`H¹₀(B_R)` is `≥ 0` a.e.; in particular the solution with source `g ≥ 0` is `≥ 0`. -/
theorem greenMaxPrinciple (d : ℕ) (hd : 2 ≤ d) (Λ R : ℝ) (hR : 0 < R) (a : CoeffField d)
    (hmeas : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x))
    (b : CoeffField d) (hb : b = a ∨ b = adjointCoeffField a) :
    (∀ v : H10Function (euclideanBall (0 : Vec d) R),
      (∀ φ : H10Function (euclideanBall (0 : Vec d) R),
        (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ φ.toH1Function.toFun x) →
        IntegrableOn (fun x => vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x)))
            (euclideanBall (0 : Vec d) R) ∧
          0 ≤ ∫ x in euclideanBall (0 : Vec d) R,
            vecDot (φ.toH1Function.grad x) (matVecMul (b x) (v.toH1Function.grad x))) →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x) ∧
    (∀ g : Vec d → ℝ, MemL2On (euclideanBall (0 : Vec d) R) g →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ g x) →
      ∀ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g
        (0 : Vec d → Vec d) →
      ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), 0 ≤ v.toH1Function.toFun x) := by exact PDE.GreenMaxPrincipleProof.result d hd Λ R hR a hmeas hell b hb

end PDE
