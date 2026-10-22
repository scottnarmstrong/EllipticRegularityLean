module

public import PDEFoundation.Analysis.Newtonian.Defs
public import PDEFoundation.Analysis.Newtonian.Kernel.Bridge
public import PDEFoundation.Analysis.Newtonian.Kernel.Holder

/-!
# Proof of `PDE.newtonKernelJacobian_holder`

`PDE.NewtonKernelHolderProof.result`: the Hölder bound for `∇E`, with the explicit constant
`|k| (d+5)² 8^(d+2) + 1`, `k = (d |B₁|)⁻¹`, from `Kernel.Holder`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace NewtonKernelHolderProof

theorem result (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z z' : Vec d, z ≠ 0 →
        vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
        ∀ v : Vec d,
          vecEuclideanNorm
              (matVecMul (newtonKernelJacobian z - newtonKernelJacobian z') v) ≤
            C * (vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1)) *
              vecEuclideanNorm v := by
  have _ := hd
  refine ⟨|newtonConst d| * ((d : ℝ) + 5) ^ 2 * 8 ^ (d + 2) + 1, by positivity,
    fun z z' hz hzz v => ?_⟩
  have h := NewtonKernelAux.kerJac_holder_aux (newtonConst d) hz hzz v
  have hX : 0 ≤ vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1) * vecEuclideanNorm v := by
    exact mul_nonneg (div_nonneg (vecEuclideanNorm_nonneg _) (pow_nonneg (vecEuclideanNorm_nonneg _) _))
      (vecEuclideanNorm_nonneg _)
  have e : newtonKernelJacobian z - newtonKernelJacobian z' =
      NewtonKernelAux.kerJac (newtonConst d) z -
        NewtonKernelAux.kerJac (newtonConst d) z' := by
    rw [NewtonKernelAux.newtonKernelJacobian_eq_kerJac, NewtonKernelAux.newtonKernelJacobian_eq_kerJac]
  rw [e]
  refine h.trans ?_
  nlinarith [hX]

end NewtonKernelHolderProof

end PDE
