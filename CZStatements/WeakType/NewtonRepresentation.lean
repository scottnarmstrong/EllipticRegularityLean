module

public import PDEFoundation.Analysis.Newtonian.NewtonRepresentationProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- Representation: smooth compactly supported `w`, `F` with `Δw = div F` satisfy `w = u_F`. -/
theorem eq_newtonPotential_of_laplacian_eq_div (d : ℕ) (hd : 0 < d)
    (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hΔ : ∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) :
    w = newtonPotential F := by exact PDE.NewtonRepresentationProof.result d hd w F hw hwc hF hFc hΔ

end PDE
