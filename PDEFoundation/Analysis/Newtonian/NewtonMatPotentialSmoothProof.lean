module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Matrix.MatPotentialSmooth

/-!
# Proof of `PDE.contDiff_newtonPotentialMat_and_coordDeriv`

Smoothness of `newtonPotentialMat M F` and the formula `∂_k u^M_F = u^M_{∂_k F}`, obtained from the
Laplacian case (`NewtonPotentialSmoothProof`) by the change of variables `x = S y`, `S Sᵀ = M`.
-/

@[expose] public section

namespace PDE

namespace NewtonMatPotentialSmoothProof

/-- Smoothness of the matrix Newton potential and the coordinate derivative formula. -/
theorem result (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (F : Vec d → Vec d) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotentialMat M F) ∧
      ∀ (k : Fin d) (x : Vec d),
        euclideanCoordDeriv k (newtonPotentialMat M F) x =
          newtonPotentialMat M (fun y i => euclideanCoordDeriv k (fun z => F z i) y) x := by
  obtain ⟨S, hS, hdet⟩ := MatChange.exists_factor (MatChange.posDef_of_ellipticity hΛ hMsymm hM)
  exact ⟨MatChange.contDiff_newtonPotentialMat hd hS hdet hF hFc,
    fun k x => MatChange.coordDeriv_newtonPotentialMat hd hS hdet hF hFc k x⟩

end NewtonMatPotentialSmoothProof

end PDE
