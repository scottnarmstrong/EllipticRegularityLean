module

public import EllipticRegularity.Ch4.Examples.CoshLower
public import PDEFoundation

/-!
# Proof of `PDE.cosh_lower_example` (Proposition 4.22)

-/

@[expose] public section

namespace PDE.CoshLowerExampleProof

open MeasureTheory

theorem result (d : ℕ) (hd : 3 ≤ d) (Cstar : ℝ)
    (hC : ENNReal.ofReal Cstar * volume (euclideanBall (0 : Vec d) 1) =
      2 * volume (euclideanBall (0 : Vec (d - 1)) 1))
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ ≤ 1 / 2) :
    ∃ A : Mat d,
      (∀ i j : Fin d, A i j = if i = j then (if i.val = 1 then Λ else 1) else 0) ∧
      IsEllipticMatrix 1 Λ A ∧
      ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
        (∀ x : Vec d, u.toFun x =
          Real.cosh (Real.sqrt Λ * x ⟨0, by omega⟩) * Real.cos (x ⟨1, by omega⟩) /
            (Real.cosh (Real.sqrt Λ * (θ / Cstar)) * Real.cos 1)) ∧
        ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
        (∀ x ∈ euclideanBall (0 : Vec d) 1, 0 < u.toFun x) ∧
        (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
            (fun i => fderiv ℝ φ x (basisVec i)) = 0) ∧
        ENNReal.ofReal (1 - θ) * volume (euclideanBall (0 : Vec d) 1) ≤
          volume {x ∈ euclideanBall (0 : Vec d) 1 | 1 ≤ u.toFun x} ∧
        essInf (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (4 * Real.exp (-(θ * Real.sqrt Λ / Cstar))) :=
  PDE.Ch4Examples.cosh_lower_example_full  d hd Cstar hC Λ hΛ θ hθ hθ'

end PDE.CoshLowerExampleProof
