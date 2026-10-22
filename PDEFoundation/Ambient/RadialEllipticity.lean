module

public import PDEFoundation.Ambient.PlanarRadialProjection
public import PDEFoundation.Ambient.CoefficientField
public import Mathlib.Tactic.NoncommRing

/-!
# Ellipticity of radial reflection coefficients
-/

@[expose] public section

namespace PDE

theorem radialReflectionMatrix_mul_self {d : ℕ} (x : Vec d) :
    radialReflectionMatrix x * radialReflectionMatrix x = (1 : Mat d) := by
  unfold radialReflectionMatrix
  noncomm_ring [radialProjectionMatrix_mul_self x]

theorem nonsing_inv_one_add_smul_radialReflectionMatrix
    {d : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (x : Vec d) :
    (1 + delta • radialReflectionMatrix x)⁻¹ =
      (1 / (1 - delta ^ 2)) •
        (1 - delta • radialReflectionMatrix x) := by
  apply Matrix.inv_eq_right_inv
  have hden : 1 - delta ^ 2 ≠ 0 := by
    nlinarith
  calc
    (1 + delta • radialReflectionMatrix x) *
        ((1 / (1 - delta ^ 2)) •
          (1 - delta • radialReflectionMatrix x)) =
        (1 / (1 - delta ^ 2)) •
          ((1 + delta • radialReflectionMatrix x) *
            (1 - delta • radialReflectionMatrix x)) := by
      rw [Matrix.mul_smul]
    _ = (1 / (1 - delta ^ 2)) •
          ((1 - delta ^ 2) • (1 : Mat d)) := by
      congr 1
      rw [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul]
      simp only [Matrix.one_mul]
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
        radialReflectionMatrix_mul_self x]
      module
    _ = 1 := by
      ext i j
      simp only [smul_smul, one_div, inv_mul_cancel₀ hden, one_smul,
        Matrix.one_apply]

private theorem matVecMul_one_add_smul {d : ℕ} (c : ℝ)
    (A : Mat d) (v : Vec d) :
    matVecMul (1 + c • A) v = v + c • matVecMul A v := by
  classical
  change (1 + c • A).mulVec v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rfl

private theorem matVecMul_one_sub_smul {d : ℕ} (c : ℝ)
    (A : Mat d) (v : Vec d) :
    matVecMul (1 - c • A) v = v - c • matVecMul A v := by
  classical
  change (1 - c • A).mulVec v = _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rfl

private theorem vecDot_add_right {d : ℕ} (u v w : Vec d) :
    vecDot u (v + w) = vecDot u v + vecDot u w := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

private theorem vecDot_sub_right {d : ℕ} (u v w : Vec d) :
    vecDot u (v - w) = vecDot u v - vecDot u w := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

private theorem vecDot_smul_right {d : ℕ} (u v : Vec d) (c : ℝ) :
    vecDot u (c • v) = c * vecDot u v := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The identity plus a subunit radial reflection is uniformly elliptic with
the exact eigenvalue bounds `1 - delta` and `1 + delta`. -/
theorem isEllipticMatrix_one_add_radialReflectionMatrix
    {d : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (x : Vec d) :
    IsEllipticMatrix (1 - delta) (1 + delta)
      (1 + delta • radialReflectionMatrix x) := by
  have hlow : 0 < 1 - delta := by linarith
  have hupper : 0 < 1 + delta := by linarith
  refine ⟨hlow, by linarith, ?_, ?_⟩
  · intro v
    rw [matVecMul_one_add_smul, vecDot_add_right,
      vecDot_smul_right]
    change (1 - delta) * vecNormSq v ≤
      vecNormSq v + delta *
        vecDot v (matVecMul (radialReflectionMatrix x) v)
    have hq := neg_vecNormSq_le_vecDot_radialReflectionMatrix x v
    nlinarith
  · intro v
    rw [nonsing_inv_one_add_smul_radialReflectionMatrix hdelta hdeltaOne]
    rw [show matVecMul
        ((1 / (1 - delta ^ 2)) •
          (1 - delta • radialReflectionMatrix x)) v =
        (1 / (1 - delta ^ 2)) •
          matVecMul (1 - delta • radialReflectionMatrix x) v by
      exact Matrix.smul_mulVec _ _ _, vecDot_smul_right,
      matVecMul_one_sub_smul, vecDot_sub_right, vecDot_smul_right]
    change (1 + delta)⁻¹ * vecNormSq v ≤
      (1 / (1 - delta ^ 2)) *
        (vecNormSq v - delta *
          vecDot v (matVecMul (radialReflectionMatrix x) v))
    have hq := vecDot_radialReflectionMatrix_le_vecNormSq x v
    have hden : 0 < 1 - delta ^ 2 := by nlinarith
    have hfactor :
        (1 + delta)⁻¹ = (1 - delta) / (1 - delta ^ 2) := by
      field_simp
      ring
    rw [hfactor]
    have hnum :
        (1 - delta) * vecNormSq v ≤
          vecNormSq v - delta *
            vecDot v (matVecMul (radialReflectionMatrix x) v) := by
      nlinarith
    calc
      (1 - delta) / (1 - delta ^ 2) * vecNormSq v =
          ((1 - delta) * vecNormSq v) / (1 - delta ^ 2) := by ring
      _ ≤ (vecNormSq v - delta *
            vecDot v (matVecMul (radialReflectionMatrix x) v)) /
          (1 - delta ^ 2) := (div_le_div_iff_of_pos_right hden).2 hnum
      _ = 1 / (1 - delta ^ 2) *
          (vecNormSq v - delta *
            vecDot v (matVecMul (radialReflectionMatrix x) v)) := by ring

/-- Rescaling by the lower eigenvalue gives unit lower ellipticity and ratio
`(1 + delta) / (1 - delta)`. -/
theorem isEllipticMatrix_normalized_radialReflectionMatrix
    {d : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta < 1)
    (x : Vec d) :
    IsEllipticMatrix 1 ((1 + delta) / (1 - delta))
      ((1 - delta)⁻¹ •
        (1 + delta • radialReflectionMatrix x)) := by
  have hscale : 0 < (1 - delta)⁻¹ := inv_pos.mpr (by linarith)
  have hbase := isEllipticMatrix_smul hscale
    (isEllipticMatrix_one_add_radialReflectionMatrix hdelta hdeltaOne x)
  convert hbase using 1
  · have hne : 1 - delta ≠ 0 := by linarith
    rw [inv_mul_cancel₀ hne]
  · rw [div_eq_mul_inv]
    ring

end PDE
