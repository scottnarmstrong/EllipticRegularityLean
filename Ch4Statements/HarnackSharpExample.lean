module

public import EllipticRegularity.Ch4.HarnackSharpExampleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Sharpness of the Harnack inequality (Proposition 4.20, first part). For `d ≥ 2`,
`Λ ≥ 1`, the constant matrix `a = e₁⊗e₁ + Λ e₂⊗e₂ + Σ_{j≥3} e_j⊗e_j` and the smooth
`u = exp(√Λ x₁) cos x₂` (`u ∈ H¹(B₁)`, `u > 0` in `B₁`, `-div a∇u = 0` in `ℝ^d`) satisfy
`sup_{B_{1/2}} u ≥ exp(√Λ) inf_{B_{1/2}} u` (read as essential sup/inf; `u` is continuous). -/
theorem harnack_sharp_example (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
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
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by exact PDE.HarnackSharpExampleProof.result d hd Λ hΛ

end PDE
