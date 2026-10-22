module

public import PDEFoundation.Analysis.Newtonian.NewtonKernelDerivProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- The Newtonian kernel `E` is smooth off the origin and its derivative at `z ≠ 0` is
`(I - d ẑ⊗ẑ)/(d|B₁||z|^d)`. -/
theorem newtonKernel_hasFDerivAt (d : ℕ) (hd : 0 < d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (newtonKernel (d := d)) {(0 : Vec d)}ᶜ ∧
      ∀ z : Vec d, z ≠ 0 →
        HasFDerivAt (newtonKernel (d := d))
          (LinearMap.toContinuousLinearMap
            (Matrix.toLin' (newtonKernelJacobian z))) z := by exact PDE.NewtonKernelDerivProof.result d hd

end PDE
