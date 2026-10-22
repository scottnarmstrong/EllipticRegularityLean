module

public import PDEFoundation.Analysis.Newtonian.NewtonWeakTypeProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- Local weak-type (1,1) estimate for `∇u_F`, `F` supported in `B₁`, with `C = C(d)`. -/
theorem exists_newtonPotential_weakTypeOne (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) := by exact PDE.NewtonWeakTypeProof.result d hd

end PDE
