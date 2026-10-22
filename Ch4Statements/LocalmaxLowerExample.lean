module

public import EllipticRegularity.Ch4.LocalmaxLowerExampleProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Lower bound `Λ^{(d-1)/4}` in the local maximum principle (Proposition 4.12,
first part). For `d ≥ 2` there is `c > 0` such that for every `Λ ≥ 1` the constant matrix
`a = diag(1,…,1,Λ)` and the explicit smooth `u = exp(x_d²/2 - s/(d-1))`,
`s = (1+Λ|x'|²)^{1/2}`, satisfy `u ∈ H¹(B₁)`, `-div a∇u ≤ 0` in `ℝ^d` (tested against
nonnegative `C_c^∞(ℝ^d)`), and `esssup_{B_{1/2}} u ≥ u(0) ≥ c Λ^{(d-1)/4} ‖u‖_{L²(B₁)}`. -/
theorem localmax_lower_example (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ∃ A : Mat d,
        (∀ i j : Fin d, A i j = if i = j then (if i.val + 1 = d then Λ else 1) else 0) ∧
        IsEllipticMatrix 1 Λ A ∧
        ∃ u : H1Function (euclideanBall (0 : Vec d) 1),
          (∀ x : Vec d, u.toFun x = Real.exp (x ⟨d - 1, by omega⟩ ^ 2 / 2 -
            Real.sqrt (1 + Λ * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val + 1 < d),
              x i ^ 2) / ((d : ℝ) - 1))) ∧
          ContDiff ℝ (⊤ : ℕ∞) u.toFun ∧
          (∀ x, 0 < u.toFun x) ∧
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
            ∫ x, vecDot (matVecMul A (fun i => fderiv ℝ u.toFun x (basisVec i)))
              (fun i => fderiv ℝ φ x (basisVec i)) ≤ 0) ∧
          essSup (fun x => ENNReal.ofReal (u.toFun x))
              (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≥
            ENNReal.ofReal (u.toFun 0) ∧
          ENNReal.ofReal (u.toFun 0) ≥
            ENNReal.ofReal (c * Λ ^ (((d : ℝ) - 1) / 4)) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by exact PDE.LocalmaxLowerExampleProof.result d hd

end PDE
