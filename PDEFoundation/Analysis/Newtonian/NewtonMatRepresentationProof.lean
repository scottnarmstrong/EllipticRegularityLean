module

public import PDEFoundation.Analysis.Newtonian.Matrix.MatRepresentationLaplace
public import PDEFoundation.Analysis.Newtonian.Matrix.ChangePotential

/-!
# Proof of `PDE.eq_newtonPotentialMat_of_div_eq_div`

If `M` is symmetric and elliptic and `w`, `F` are smooth with compact support with
`div (M ∇w) = div F`, then `w = newtonPotentialMat M F`.  Choose `S` with `S Sᵀ = M`; then
`v = w ∘ S` and `G = S⁻¹ F ∘ S` satisfy `Δ v = div G`, hence `v = newtonPotential G`, and the
change of variables `ChangePotential` identifies the potentials.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonMatRepresentationProof

theorem result (d : ℕ) (hd : 0 < d)
    (Λ : ℝ) (hΛ : 0 < Λ) (M : Mat d) (hMsymm : M.IsSymm)
    (hM : ∀ ξ : Vec d,
      Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul M ξ) ∧
        vecDot ξ (matVecMul M ξ) ≤ Λ * vecNormSq ξ)
    (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hdiv : ∀ x, classicalDivergence
      (fun y => matVecMul M (classicalGradient w y)) x = classicalDivergence F x) :
    w = newtonPotentialMat M F := by
  obtain ⟨S, hS, hdet⟩ := MatChange.exists_factor (MatChange.posDef_of_ellipticity hΛ hMsymm hM)
  have hv : ContDiff ℝ (⊤ : ℕ∞) fun y => w (matVecMul S y) :=
    hw.comp (MatChange.contDiff_matVecMul S)
  have hG : ContDiff ℝ (⊤ : ℕ∞) fun y => matVecMul S⁻¹ (F (matVecMul S y)) :=
    (MatChange.contDiff_matVecMul S⁻¹).comp (hF.comp (MatChange.contDiff_matVecMul S))
  have hΔ : ∀ y, euclideanCoordLaplacian (fun z => w (matVecMul S z)) y =
      classicalDivergence (fun z => matVecMul S⁻¹ (F (matVecMul S z))) y := by
    intro y
    rw [MatChange.euclideanCoordLaplacian_comp_matVecMul S hw, hS, hdiv,
      MatChange.classicalDivergence_inv_comp hdet hF]
  have hrep := MatChange.eq_newtonPotential_of_laplacian d hd _ _ hv
    (MatChange.hasCompactSupport_comp_matVecMul hdet hwc) hG
    (MatChange.hasCompactSupport_matVecMul_comp hdet hFc) hΔ
  funext x
  have hx : w x = w (matVecMul S (matVecMul S⁻¹ x)) := by
    rw [MatChange.matVecMul_matVecMul, MatChange.mul_inv_self hdet, MatChange.matVecMul_one]
  rw [hx]
  exact (congrFun hrep (matVecMul S⁻¹ x)).trans (MatChange.newtonPotential_transform hS hdet F x)

end NewtonMatRepresentationProof

end PDE
