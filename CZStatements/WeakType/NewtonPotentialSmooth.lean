module

public import PDEFoundation.Analysis.Newtonian.NewtonPotentialSmoothProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- For smooth compactly supported `F`, the Newtonian potential `u_F` is smooth and
`∂_k u_F = Σ_i E_i ⋆ ∂_k F_i`. -/
theorem contDiff_newtonPotential_and_coordDeriv (d : ℕ) (hd : 0 < d)
    (F : Vec d → Vec d) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotential F) ∧
      ∀ (k : Fin d) (x : Vec d),
        euclideanCoordDeriv k (newtonPotential F) x =
          ∫ y, vecDot (newtonKernel (x - y))
            (fun i => euclideanCoordDeriv k (fun z => F z i) y) := by exact PDE.NewtonPotentialSmoothProof.result d hd F hF hFc

end PDE
