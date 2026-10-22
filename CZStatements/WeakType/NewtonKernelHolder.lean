module

public import PDEFoundation.Analysis.Newtonian.NewtonKernelHolderProof

@[expose] public section

open MeasureTheory

namespace PDE

/-- Hölder bound for `∇E` in the Euclidean operator norm:
`|∇E(z) - ∇E(z')| ≤ C(d) |z - z'| / |z|^{d+1}` when `|z - z'| ≤ |z|/2`. -/
theorem newtonKernelJacobian_holder (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z z' : Vec d, z ≠ 0 →
        vecEuclideanNorm (z - z') ≤ vecEuclideanNorm z / 2 →
        ∀ v : Vec d,
          vecEuclideanNorm
              (matVecMul (newtonKernelJacobian z - newtonKernelJacobian z') v) ≤
            C * (vecEuclideanNorm (z - z') / vecEuclideanNorm z ^ (d + 1)) *
              vecEuclideanNorm v := by exact PDE.NewtonKernelHolderProof.result d hd

end PDE
