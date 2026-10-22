module

public import PDEFoundation.Analysis.Newtonian.NewtonMatPotentialSmoothProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- For a constant symmetric elliptic matrix `M` and smooth compactly supported `F`, the
potential `u^M_F` is smooth and `∂_k u^M_F = u^M_{∂_k F}`. -/
theorem contDiff_newtonPotentialMat_and_coordDeriv (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (F : Vec d → Vec d) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotentialMat M F) ∧
      ∀ (k : Fin d) (x : Vec d),
        euclideanCoordDeriv k (newtonPotentialMat M F) x =
          newtonPotentialMat M (fun y i => euclideanCoordDeriv k (fun z => F z i) y) x := by exact PDE.NewtonMatPotentialSmoothProof.result d hd Λ hΛ M hMsymm hM F hF hFc

end PDE
