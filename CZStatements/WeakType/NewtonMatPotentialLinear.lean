module

public import PDEFoundation.Analysis.Newtonian.NewtonMatPotentialLinearProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- `F ↦ u^M_F` is linear on continuous compactly supported fields:
for a finite family `F i` and coefficients `c i`. -/
theorem newtonPotentialMat_linearCombination {ι : Type*} (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (s : Finset ι) (c : ι → ℝ) (F : ι → Vec d → Vec d)
    (hF : ∀ i ∈ s, Continuous (F i)) (hFc : ∀ i ∈ s, HasCompactSupport (F i)) :
    newtonPotentialMat M (∑ i ∈ s, c i • F i) =
      ∑ i ∈ s, c i • newtonPotentialMat M (F i) := by exact PDE.NewtonMatPotentialLinearProof.result d hd Λ hΛ M hMsymm hM s c F hF hFc

end PDE
