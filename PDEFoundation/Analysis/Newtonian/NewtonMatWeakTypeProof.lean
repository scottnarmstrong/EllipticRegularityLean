module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Matrix.MatWeakTypeMain
public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyFinal

/-!
# Proof of `PDE.exists_newtonPotentialMat_weakTypeOne`

The constant-matrix estimate follows from the Laplacian estimate `NewtonWeakType` by the linear
change of variables `x = S y`, `S Sᵀ = M`, together with a dilation by `√Λ`
(see `PDEFoundation.Analysis.Newtonian.Matrix.MatWeakTypeMain`), with `C = C₀ Λ`.

`resultOfLaplace` proves the statement from the Laplacian estimate given as a hypothesis; `result`
applies it to `PDE.NewtonWeakType.exists_weakType`, the proof of the Laplacian estimate.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonMatWeakTypeProof

/-- The matrix estimate from the Laplacian estimate (statement of `exists_newtonPotential_weakTypeOne`). -/
theorem resultOfLaplace (d : ℕ) (hd : 0 < d)
    (hLaplace : ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)))
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : Mat d, M.IsSymm →
        (∀ ξ : Vec d,
          Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
            vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ) →
        ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
          tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
          ∀ lam : ℝ, 0 < lam →
            volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
                lam < vecEuclideanNorm
                  (classicalGradient (newtonPotentialMat M F) x)} ≤
              ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) := by
  obtain ⟨C₀, hC₀, h⟩ := hLaplace
  exact ⟨C₀ * Λ, mul_pos hC₀ hΛ, fun M hMs hM F hF hFs lam hlam =>
    MatChange.weakType_mat hd h hC₀.le hΛ hMs hM hF hFs hlam⟩

/-- The constant-matrix weak-type (1,1) estimate, from the Laplacian case. -/
theorem result (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : Mat d, M.IsSymm →
        (∀ ξ : Vec d,
          Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
            vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ) →
        ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
          tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
          ∀ lam : ℝ, 0 < lam →
            volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
                lam < vecEuclideanNorm
                  (classicalGradient (newtonPotentialMat M F) x)} ≤
              ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) :=
  resultOfLaplace d hd (PDE.NewtonWeakType.exists_weakType d hd) Λ hΛ

end NewtonMatWeakTypeProof

end PDE
