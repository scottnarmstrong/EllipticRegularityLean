module

public import PDEFoundation.Ambient.Matrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Native continuous linear equivalences from invertible matrices
-/

@[expose] public section

namespace PDE

noncomputable section

/-- An invertible native matrix, regarded as a continuous linear equivalence
of the native vector carrier. -/
noncomputable def matrixContinuousLinearEquiv {d : ℕ} (A : Mat d) (hA : IsUnit A) :
    Vec d ≃L[ℝ] Vec d :=
  ({
    toFun := Matrix.toLin' A
    invFun := Matrix.toLin' A⁻¹
    left_inv := fun x => by
      change A⁻¹.mulVec (A.mulVec x) = x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
        (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    right_inv := fun x => by
      change A.mulVec (A⁻¹.mulVec x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
        (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    map_add' := (Matrix.toLin' A).map_add
    map_smul' := (Matrix.toLin' A).map_smul
  } : Vec d ≃ₗ[ℝ] Vec d).toContinuousLinearEquiv

@[simp]
theorem matrixContinuousLinearEquiv_apply {d : ℕ} (A : Mat d) (hA : IsUnit A)
    (x : Vec d) :
    matrixContinuousLinearEquiv A hA x = matVecMul A x :=
  rfl

@[simp]
theorem matrixContinuousLinearEquiv_symm_apply {d : ℕ} (A : Mat d) (hA : IsUnit A)
    (x : Vec d) :
    (matrixContinuousLinearEquiv A hA).symm x = matVecMul A⁻¹ x :=
  rfl

end

end PDE
