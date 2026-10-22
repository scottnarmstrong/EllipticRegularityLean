module

public import PDEFoundation.Analysis.RadialModeGradient
public import PDEFoundation.Ambient.RadialEllipticity

/-!
# Flux of radial coordinate modes
-/

@[expose] public section

namespace PDE

/-- The literal coefficient flux of a coordinate radial mode. -/
noncomputable def radialCoefficientFlux {d : ℕ}
    (delta : ℝ) (k : Fin d) (β : ℝ) (x : Vec d) : Vec d :=
  matVecMul (1 + delta • radialReflectionMatrix x)
    (radialModePowerField k β x)

private theorem matVecMul_radialProjectionMatrix_projection_action
    {d : ℕ} (x v : Vec d) :
    matVecMul (radialProjectionMatrix x)
        (matVecMul (radialProjectionMatrix x) v) =
      matVecMul (radialProjectionMatrix x) v := by
  change (radialProjectionMatrix x).mulVec
      ((radialProjectionMatrix x).mulVec v) =
    (radialProjectionMatrix x).mulVec v
  rw [Matrix.mulVec_mulVec, radialProjectionMatrix_mul_self]

private theorem matVecMul_radialReflectionMatrix_radialModeVector
    {d : ℕ} (k : Fin d) (β : ℝ) (x : Vec d) :
    matVecMul (radialReflectionMatrix x) (radialModeVector k β x) =
      -basisVec k +
        (β + 1) • matVecMul (radialProjectionMatrix x) (basisVec k) := by
  rw [radialModeVector_eq_projection_action]
  change (2 • radialProjectionMatrix x - 1).mulVec
      (basisVec k +
        (β - 1) • (radialProjectionMatrix x).mulVec (basisVec k)) = _
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [show (radialProjectionMatrix x).mulVec
      ((radialProjectionMatrix x).mulVec (basisVec k)) =
      (radialProjectionMatrix x).mulVec (basisVec k) from
    matVecMul_radialProjectionMatrix_projection_action x (basisVec k)]
  rw [show (radialProjectionMatrix x).mulVec (basisVec k) =
      (x k / vecNormSq x) • x from
    matVecMul_radialProjectionMatrix x (basisVec k) |>.trans (by
      rw [vecDot_basisVec_right])]
  ext i
  simp
  ring

/-- Exact algebraic decomposition of the radial coefficient flux away from
the origin. -/
theorem radialCoefficientFlux_eq
    {d : ℕ} (delta : ℝ) (k : Fin d) (β : ℝ) (x : Vec d) :
    radialCoefficientFlux delta k β x =
      Real.rpow (vecEuclideanNorm x) (β - 1) •
        ((1 - delta) • basisVec k +
          (((1 + delta) * β - (1 - delta)) *
            (x k / vecNormSq x)) • x) := by
  rw [radialCoefficientFlux, radialModePowerField]
  change (1 + delta • radialReflectionMatrix x).mulVec
      (Real.rpow (vecEuclideanNorm x) (β - 1) •
        radialModeVector k β x) = _
  rw [Matrix.mulVec_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  rw [show (radialReflectionMatrix x).mulVec (radialModeVector k β x) =
      -basisVec k +
        (β + 1) • (radialProjectionMatrix x).mulVec (basisVec k) from
    matVecMul_radialReflectionMatrix_radialModeVector k β x]
  rw [radialModeVector_eq_projection_action]
  rw [show (radialProjectionMatrix x).mulVec (basisVec k) =
      (x k / vecNormSq x) • x from
    matVecMul_radialProjectionMatrix x (basisVec k) |>.trans (by
      rw [vecDot_basisVec_right])]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    basisVec_apply]
  rw [matVecMul_radialProjectionMatrix, vecDot_basisVec_right]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst i
    simp only [ite_true]
    ring
  · simp only [hik, ite_false]
    ring

end PDE
