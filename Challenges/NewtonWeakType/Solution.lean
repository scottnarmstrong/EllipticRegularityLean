module

public import PDEFoundation.Analysis.Newtonian.NewtonWeakTypeProof

@[expose] public section

open scoped ENNReal NNReal

namespace PDE

open MeasureTheory

/-- Local weak-type `(1,1)` estimate for the gradient of the Newtonian potential `u_F` of a smooth
field `F` supported in `B₁`: there is `C = C(d)` such that
`|{x ∈ B₂ : |∇u_F(x)| > λ}| ≤ C λ⁻¹ ‖F‖_{L¹}` for every `λ > 0`. -/
theorem exists_newtonPotential_weakTypeOne (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) :=
  PDE.NewtonWeakTypeProof.result d hd

end PDE
