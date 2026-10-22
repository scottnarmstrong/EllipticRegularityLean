module

public import PDEFoundation.Analysis.Newtonian.WeakType.Energy
public import PDEFoundation.Analysis.Newtonian.NewtonRepresentationProof

/-!
# The L² energy bound for the Newtonian potential

Unconditional forms of `lintegral_gradient_newtonPotential_sq_le` and
`volume_gradient_newtonPotential_gt_le`: their representation hypothesis is discharged by
`PDE.NewtonRepresentationProof.result`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.NewtonWeakType

variable {d : ℕ}

/-- `‖∇u_h‖_{L²(ℝ^d)} ≤ ‖h‖_{L²(ℝ^d)}` for smooth compactly supported `h`. -/
theorem lintegral_gradient_newtonPotential_sq_le' (hd : 0 < d)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    ∫⁻ x, ENNReal.ofReal (vecNormSq (classicalGradient (newtonPotential h) x)) ≤
      ∫⁻ x, ENNReal.ofReal (vecNormSq (h x)) :=
  lintegral_gradient_newtonPotential_sq_le hd
    (fun w F hw hwc hF hFc hΔ => PDE.NewtonRepresentationProof.result d hd w F hw hwc hF hFc hΔ)
    hh hhc

/-- Chebyshev form: `|{|∇u_h| > λ}| ≤ λ⁻² ∫ |h|²` for smooth compactly supported `h`. -/
theorem volume_gradient_newtonPotential_gt_le' (hd : 0 < d)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    {l : ℝ} (hl : 0 < l) :
    volume {x | l < vecEuclideanNorm (classicalGradient (newtonPotential h) x)} ≤
      ENNReal.ofReal (l⁻¹ ^ 2 * ∫ x, vecNormSq (h x)) :=
  volume_gradient_newtonPotential_gt_le hd
    (fun w F hw hwc hF hFc hΔ => PDE.NewtonRepresentationProof.result d hd w F hw hwc hF hFc hΔ)
    hh hhc hl

end PDE.NewtonWeakType
