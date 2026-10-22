module

public import PDEFoundation.Sobolev.ClassicalLaplacian
public import PDEFoundation.Ambient.Matrix
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Newton kernel and potential on native vectors

All objects live on `Vec d` and `Mat d`; norms are the explicit Euclidean ones
(`vecEuclideanNorm`, `vecDot`).  The kernel `E(z) = z / (d |B₁| |z|^d)` is the
gradient of the fundamental solution of the Laplacian (`div E = δ`), and
`newtonPotential F x = ∫ E(x - y) · F(y) dy` solves `Δu = div F`.
-/

/-!
# Newtonian kernel and potential

Definitions: the kernel `E(z) = z/(d|B₁||z|^d)`, its Jacobian formula, the potential `u_F = ∫ E(x-y)·F(y) dy`,
the constant-matrix kernel and potential, and the classical divergence of a vector field.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

/-- The classical divergence `Σ_k ∂_k F_k` of a vector field (coordinate
derivatives via `fderiv` on basis vectors). -/
def classicalDivergence {d : ℕ} (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∑ k : Fin d, euclideanCoordDeriv k (fun y => F y k) x

/-- The gradient of the fundamental solution of the Laplacian:
`E(z) = z / (d |B₁| |z|^d)`, with `E 0 = 0` (division by zero). -/
def newtonKernel {d : ℕ} (z : Vec d) : Vec d :=
  (1 / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
    vecEuclideanNorm z ^ d)) • z

/-- The matrix `(I - d ẑ⊗ẑ) / (d |B₁| |z|^d)`, the Jacobian of `newtonKernel`
away from `0`, with `ẑ ⊗ ẑ = z zᵀ / |z|²`. -/
def newtonKernelJacobian {d : ℕ} (z : Vec d) : Mat d :=
  fun i j =>
    ((if i = j then (1 : ℝ) else 0) - (d : ℝ) * (z i * z j) / vecNormSq z) /
      ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
        vecEuclideanNorm z ^ d)

/-- The Newton potential `x ↦ ∫ E(x - y) · F(y) dy` of the field `F`. -/
def newtonPotential {d : ℕ} (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y, vecDot (newtonKernel (x - y)) (F y)

/-- The kernel of `div (M ∇ ·)`:
`E_M(z) = M⁻¹ z / (d |B₁| √(det M) (zᵀ M⁻¹ z)^(d/2))`. -/
def newtonKernelMat {d : ℕ} (M : Mat d) (z : Vec d) : Vec d :=
  (1 / ((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal *
    Real.sqrt M.det * (vecDot z (matVecMul M⁻¹ z)) ^ ((d : ℝ) / 2))) •
    matVecMul M⁻¹ z

/-- The potential `x ↦ ∫ E_M(x - y) · F(y) dy`. -/
def newtonPotentialMat {d : ℕ} (M : Mat d) (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y, vecDot (newtonKernelMat M (x - y)) (F y)

end

end PDE
