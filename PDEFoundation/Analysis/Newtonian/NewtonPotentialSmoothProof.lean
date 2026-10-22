module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Potential.Smooth

/-!
# Proof of `PDE.contDiff_newtonPotential_and_coordDeriv`

For smooth compactly supported `F`, the Newton potential is smooth and its coordinate derivatives are
`∂_k u_F = Σ_i E_i ⋆ ∂_k F_i`.  The proof writes `u_F` as a sum of Mathlib convolutions of the
(locally integrable) kernel components with the components of `F`; see
`PDEFoundation.Analysis.Newtonian.Potential.Smooth`.
-/

@[expose] public section

namespace PDE

namespace NewtonPotentialSmoothProof

/-- Smoothness of the Newton potential and the coordinate derivative formula. -/
theorem result (d : ℕ) (hd : 0 < d)
    (F : Vec d → Vec d) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    ContDiff ℝ (⊤ : ℕ∞) (newtonPotential F) ∧
      ∀ (k : Fin d) (x : Vec d),
        euclideanCoordDeriv k (newtonPotential F) x =
          ∫ y, vecDot (newtonKernel (x - y))
            (fun i => euclideanCoordDeriv k (fun z => F z i) y) :=
  ⟨contDiff_newtonPotential hd hF hFc, coordDeriv_newtonPotential hd hF hFc⟩

end NewtonPotentialSmoothProof

end PDE
