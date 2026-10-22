module

public import EllipticRegularity.Ch4.Examples.HarnackSharp
public import PDEFoundation

/-!
# Proof of `PDE.harnack_sharp_example` (Proposition 4.20)

-/

@[expose] public section

namespace PDE.HarnackSharpExampleProof

open MeasureTheory

theorem result (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.exp (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩)) ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        ENNReal.ofReal (Real.exp (Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
  PDE.Ch4Examples.harnack_sharp_example_full  d hd Λ hΛ

end PDE.HarnackSharpExampleProof
