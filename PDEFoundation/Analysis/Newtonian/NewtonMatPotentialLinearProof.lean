module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Matrix.MatPotentialLinear

/-!
# Proof of `PDE.newtonPotentialMat_linearCombination`

`F ↦ newtonPotentialMat M F` is linear on continuous compactly supported fields.  Choose `S` with
`S Sᵀ = M`; each integrand is integrable by the change of variables to the Laplacian kernel.
-/

@[expose] public section

namespace PDE

namespace NewtonMatPotentialLinearProof

/-- Linearity of the matrix Newton potential over finite linear combinations. -/
theorem result {ι : Type*} (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (s : Finset ι) (c : ι → ℝ) (F : ι → Vec d → Vec d)
    (hF : ∀ i ∈ s, Continuous (F i)) (hFc : ∀ i ∈ s, HasCompactSupport (F i)) :
    newtonPotentialMat M (∑ i ∈ s, c i • F i) =
      ∑ i ∈ s, c i • newtonPotentialMat M (F i) := by
  obtain ⟨S, hS, hdet⟩ := MatChange.exists_factor (MatChange.posDef_of_ellipticity hΛ hMsymm hM)
  exact MatChange.newtonPotentialMat_linearCombination hd hS hdet s c F hF hFc

end NewtonMatPotentialLinearProof

end PDE
