module

public import PDEFoundation.Analysis.Newtonian.NewtonMatWeakTypeProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- Local weak-type (1,1) estimate for the constant-matrix potential, with `C = C(d, Λ)`. -/
theorem exists_newtonPotentialMat_weakTypeOne (d : ℕ) (hd : 0 < d)
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
              ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) := by exact PDE.NewtonMatWeakTypeProof.result d hd Λ hΛ

end PDE
