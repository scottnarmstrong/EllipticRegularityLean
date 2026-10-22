module

public import EllipticRegularity.Ch4.ExistsSharp2dHolderConstantProof

@[expose] public section

namespace PDE

open MeasureTheory

/-- Sharp Hölder exponent in `d = 2` (Proposition 4.27(i)).
For symmetric `a` with (4.1) and a weak solution `u ∈ H¹(B_1)`: the growth bound
`∫_{B_r(x₀)}|∇u|² ≤ Λ (2r)^{2α_Λ} ∫_{B_1}|∇u|²` and a `C^{0,Λ^{-1/2}}(B_{1/2})` representative
with seminorm at most `C Λ ‖∇u‖_{L²(B_1)}`, `C` absolute. -/
theorem exists_sharp2d_holder_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField 2),
      (∀ i j : Fin 2, AEMeasurable (fun x => a x i j)
        (volumeOn (euclideanBall (0 : Vec 2) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, ∀ i j : Fin 2, a x i j = a x j i) →
      (∀ x ∈ euclideanBall (0 : Vec 2) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec 2) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec 2) 1) u (0 : Vec 2 → ℝ) 0 →
        (∀ x₀ ∈ euclideanBall (0 : Vec 2) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
          ∫ y in euclideanBall x₀ r, vecNormSq (u.grad y) ≤
            Λ * (2 * r) ^ (2 * Λ ^ (-(1 / 2 : ℝ))) *
              ∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) ∧
        ∃ (v : Vec 2 → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec 2) (1 / 2))] u.toFun ∧
          0 ≤ M ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec 2) (1 / 2)) v
            (Λ ^ (-(1 / 2 : ℝ))) M ∧
          M ≤ C * Λ * Real.sqrt (∫ y in euclideanBall (0 : Vec 2) 1, vecNormSq (u.grad y)) := by exact PDE.ExistsSharp2dHolderConstantProof.result 

end PDE
