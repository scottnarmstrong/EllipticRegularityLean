module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Kernel.Bridge

/-!
# Proof of `PDE.newtonKernel_hasFDerivAt`

`PDE.NewtonKernelDerivProof.result`: the Newtonian kernel is smooth off `0` with the
Jacobian `newtonKernelJacobian`; proved from the generic radial kernel in
`PDEFoundation.Analysis.Newtonian.Kernel.Deriv`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonKernelDerivProof

theorem result (d : ℕ) (hd : 0 < d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (newtonKernel (d := d)) {(0 : Vec d)}ᶜ ∧
      ∀ z : Vec d, z ≠ 0 →
        HasFDerivAt (newtonKernel (d := d))
          (LinearMap.toContinuousLinearMap
            (Matrix.toLin' (newtonKernelJacobian z))) z := by
  have _ := hd
  refine ⟨?_, fun z hz => ?_⟩
  · rw [NewtonKernelAux.newtonKernel_eq_kerField]
    exact NewtonKernelAux.kerField_contDiffOn _
  · rw [NewtonKernelAux.newtonKernel_eq_kerField, NewtonKernelAux.newtonKernelJacobian_eq_kerJac]
    exact NewtonKernelAux.kerField_hasFDerivAt _ hz

end NewtonKernelDerivProof

end PDE
