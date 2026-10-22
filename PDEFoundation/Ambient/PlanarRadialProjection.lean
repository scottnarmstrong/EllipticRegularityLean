module

public import PDEFoundation.Ambient.MatrixPerturbation

/-!
# Radial projections and reflections

This file records the coordinate algebra for the radial rank-one projection
and its associated reflection on the native vector carrier.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The radial rank-one projection matrix. At the origin this is the zero
matrix, according to the usual division convention in `ℝ`. -/
noncomputable def radialProjectionMatrix {d : ℕ} (x : Vec d) : Mat d :=
  fun i j => x i * x j / vecNormSq x

/-- The reflection which fixes the radial direction and negates its
orthogonal complement. At the origin it is `-1`. -/
noncomputable def radialReflectionMatrix {d : ℕ} (x : Vec d) : Mat d :=
  2 • radialProjectionMatrix x - 1

@[simp]
theorem radialProjectionMatrix_apply {d : ℕ} (x : Vec d) (i j : Fin d) :
    radialProjectionMatrix x i j = x i * x j / vecNormSq x :=
  rfl

theorem radialProjectionMatrix_symmetric {d : ℕ} (x : Vec d) :
    matTranspose (radialProjectionMatrix x) = radialProjectionMatrix x := by
  ext i j
  simp only [matTranspose_apply, radialProjectionMatrix_apply]
  rw [mul_comm]

theorem matVecMul_radialProjectionMatrix {d : ℕ} (x v : Vec d) :
    matVecMul (radialProjectionMatrix x) v =
      (vecDot x v / vecNormSq x) • x := by
  ext i
  simp only [matVecMul_apply, radialProjectionMatrix_apply, Pi.smul_apply,
    smul_eq_mul, vecDot]
  calc
    (∑ j, x i * x j / vecNormSq x * v j) =
        ∑ j, (x i / vecNormSq x) * (x j * v j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (x i / vecNormSq x) * ∑ j, x j * v j := by
      rw [Finset.mul_sum]
    _ = (∑ j, x j * v j) / vecNormSq x * x i := by ring

theorem matVecMul_radialProjectionMatrix_self {d : ℕ} (x : Vec d) :
    matVecMul (radialProjectionMatrix x) x = x := by
  rw [matVecMul_radialProjectionMatrix]
  by_cases hx : vecNormSq x = 0
  · rw [vecNormSq_eq_zero hx]
    simp
  · have hx' : vecDot x x ≠ 0 := by simpa only [vecNormSq] using hx
    simp only [vecNormSq, div_self hx', one_smul]

theorem radialProjectionMatrix_mul_self {d : ℕ} (x : Vec d) :
    radialProjectionMatrix x * radialProjectionMatrix x =
      radialProjectionMatrix x := by
  ext i j
  simp only [Matrix.mul_apply, radialProjectionMatrix_apply]
  by_cases hx : vecNormSq x = 0
  · rw [vecNormSq_eq_zero hx]
    simp
  · rw [show (∑ k : Fin d, (x i * x k / vecNormSq x) *
        (x k * x j / vecNormSq x)) =
        x i * x j / (vecNormSq x) ^ 2 *
          ∑ k : Fin d, x k * x k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      field_simp]
    rw [show (∑ k : Fin d, x k * x k) = vecNormSq x by rfl]
    field_simp

private theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem vecDot_smul_left {d : ℕ} (x y : Vec d) (c : ℝ) :
    vecDot (c • x) y = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_right, vecDot_comm]

private theorem vecDot_sub_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp [vecDot, mul_sub, Finset.sum_sub_distrib]

theorem vecNormSq_matVecMul_radialReflectionMatrix {d : ℕ}
    (x v : Vec d) :
    vecNormSq (matVecMul (radialReflectionMatrix x) v) = vecNormSq v := by
  have haction : matVecMul (radialReflectionMatrix x) v =
      2 • matVecMul (radialProjectionMatrix x) v - v := by
    classical
    change (2 • radialProjectionMatrix x - 1).mulVec v = _
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [haction, matVecMul_radialProjectionMatrix]
  by_cases hx : vecNormSq x = 0
  · rw [hx]
    simp [vecNormSq_neg]
  · have hratio : (vecDot x v / vecNormSq x) * vecNormSq x =
        vecDot x v := by field_simp
    let a : ℝ := vecDot x v / vecNormSq x
    have ha : a * vecNormSq x = vecDot x v := hratio
    have ha2 : a ^ 2 * vecNormSq x = a * vecDot x v := by
      calc
        a ^ 2 * vecNormSq x = a * (a * vecNormSq x) := by ring
        _ = a * vecDot x v := by rw [ha]
    rw [show 2 • ((vecDot x v / vecNormSq x) • x) - v =
        (2 * (vecDot x v / vecNormSq x)) • x + (-v) by
      ext i
      simp
      ring]
    rw [vecNormSq_add_expand, vecNormSq_smul, vecNormSq_neg,
      vecDot_smul_left]
    have hneg : vecDot x (-v) = -vecDot x v := by
      simp [vecDot]
    rw [hneg]
    change (2 * a) ^ 2 * vecNormSq x +
      2 * (2 * a * -vecDot x v) + vecNormSq v = vecNormSq v
    nlinarith [ha2]

theorem vecEuclideanNorm_matVecMul_radialReflectionMatrix {d : ℕ}
    (x v : Vec d) :
    vecEuclideanNorm (matVecMul (radialReflectionMatrix x) v) =
      vecEuclideanNorm v := by
  unfold vecEuclideanNorm
  rw [vecNormSq_matVecMul_radialReflectionMatrix]

theorem neg_vecNormSq_le_vecDot_radialReflectionMatrix {d : ℕ}
    (x v : Vec d) :
    -vecNormSq v ≤ vecDot v (matVecMul (radialReflectionMatrix x) v) := by
  have h := abs_vecDot_le_vecEuclideanNorm_mul v
    (matVecMul (radialReflectionMatrix x) v)
  rw [vecEuclideanNorm_matVecMul_radialReflectionMatrix] at h
  have hsq : vecEuclideanNorm v * vecEuclideanNorm v = vecNormSq v := by
    nlinarith [vecEuclideanNorm_sq v]
  rw [hsq] at h
  exact neg_le_of_abs_le h

theorem vecDot_radialReflectionMatrix_le_vecNormSq {d : ℕ}
    (x v : Vec d) :
    vecDot v (matVecMul (radialReflectionMatrix x) v) ≤ vecNormSq v := by
  have h := abs_vecDot_le_vecEuclideanNorm_mul v
    (matVecMul (radialReflectionMatrix x) v)
  rw [vecEuclideanNorm_matVecMul_radialReflectionMatrix] at h
  have hsq : vecEuclideanNorm v * vecEuclideanNorm v = vecNormSq v := by
    nlinarith [vecEuclideanNorm_sq v]
  rw [hsq] at h
  exact le_trans (le_abs_self _) h

theorem isMatrixPerturbationLE_one_add_radialReflectionMatrix
    {d : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) (x : Vec d) :
    IsMatrixPerturbationLE delta
      (1 + delta • radialReflectionMatrix x) (1 : Mat d) := by
  intro v
  have haction : matVecMul
      ((1 + delta • radialReflectionMatrix x) - 1) v =
      delta • matVecMul (radialReflectionMatrix x) v := by
    classical
    change ((1 + delta • radialReflectionMatrix x) - 1).mulVec v = _
    rw [show (1 + delta • radialReflectionMatrix x) - 1 =
        delta • radialReflectionMatrix x by abel]
    exact Matrix.smul_mulVec delta (radialReflectionMatrix x) v
  rw [haction, vecEuclideanNorm_smul, abs_of_nonneg hdelta,
    vecEuclideanNorm_matVecMul_radialReflectionMatrix]

end PDE
