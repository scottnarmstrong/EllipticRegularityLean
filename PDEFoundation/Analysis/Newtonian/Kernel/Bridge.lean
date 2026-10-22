module

public import PDEFoundation.Analysis.Newtonian.Kernel.Deriv

/-!
# Bridge from the Newton kernel definitions to the generic radial kernel

With `k = (d |B₁|)⁻¹`, `newtonKernel = kerField k` and `newtonKernelJacobian = kerJac k`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

/-- The constant `1 / (d |B₁|)` in the Newton kernel. -/
noncomputable def newtonConst (d : ℕ) : ℝ :=
  1 / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal)

namespace NewtonKernelAux

theorem newtonKernel_eq_kerField (d : ℕ) :
    (newtonKernel (d := d)) = kerField (newtonConst d) := by
  funext z
  simp only [newtonKernel, kerField, kerProfile, newtonConst, vecEuclideanNorm, one_div, mul_inv]

theorem newtonKernelJacobian_eq_kerJac (d : ℕ) (z : Vec d) :
    newtonKernelJacobian z = kerJac (newtonConst d) z := by
  funext i j
  simp only [newtonKernelJacobian, kerJac, kerProfile, newtonConst, vecEuclideanNorm, one_mul, div_eq_mul_inv,
    mul_inv]

end NewtonKernelAux

end PDE
