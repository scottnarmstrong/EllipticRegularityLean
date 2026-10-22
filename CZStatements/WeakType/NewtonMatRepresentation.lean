module

public import PDEFoundation.Analysis.Newtonian.NewtonMatRepresentationProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- Representation for `div(M∇w) = div F` with a constant symmetric elliptic matrix `M`. -/
theorem eq_newtonPotentialMat_of_div_eq_div (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hdiv : ∀ x, classicalDivergence
      (fun y => matVecMul M (classicalGradient w y)) x = classicalDivergence F x) :
    w = newtonPotentialMat M F := by exact PDE.NewtonMatRepresentationProof.result d hd Λ hΛ M hMsymm hM w F hw hwc hF hFc hdiv

end PDE
