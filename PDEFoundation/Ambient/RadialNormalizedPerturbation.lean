module

public import PDEFoundation.Ambient.RadialPerturbationSize
public import PDEFoundation.Ambient.MatAppendPerturbation

/-! # The exact oscillation size after coefficient normalization -/

@[expose] public section

namespace PDE

/-- Scalar multiplication of the radial coefficient and its average scales
the exact Euclidean perturbation action by the same scalar. -/
theorem vecEuclideanNorm_smul_radialReflectionMatrix_perturbation_action
    {d : ℕ} (c δ : ℝ) (x v : Vec d) :
    vecEuclideanNorm (matVecMul
      (c • ((1 : Mat d) + δ • radialReflectionMatrix x) - c • (1 : Mat d)) v) =
      |c * δ| * vecEuclideanNorm v := by
  have hmatrix : c • ((1 : Mat d) + δ • radialReflectionMatrix x) -
      c • (1 : Mat d) = (c * δ) • radialReflectionMatrix x := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hmatrix]
  change vecEuclideanNorm (((c * δ) • radialReflectionMatrix x).mulVec v) = _
  rw [Matrix.smul_mulVec, vecEuclideanNorm_smul]
  change |c * δ| * vecEuclideanNorm (matVecMul (radialReflectionMatrix x) v) = _
  rw [vecEuclideanNorm_matVecMul_radialReflectionMatrix]

/-- In positive dimension this action gives the exact operator threshold,
including necessity from a coordinate-vector test. -/
theorem isMatrixPerturbationLE_smul_one_add_radialReflectionMatrix_iff
    {d : ℕ} (hd : 0 < d) (c δ ε : ℝ) (x : Vec d) :
    IsMatrixPerturbationLE ε
      (c • ((1 : Mat d) + δ • radialReflectionMatrix x)) (c • (1 : Mat d)) ↔
      |c * δ| ≤ ε := by
  constructor
  · intro h
    have hv := h (basisVec ⟨0, hd⟩)
    rw [vecEuclideanNorm_smul_radialReflectionMatrix_perturbation_action,
      vecEuclideanNorm_basisVec, mul_one, mul_one] at hv
    exact hv
  · intro h v
    rw [vecEuclideanNorm_smul_radialReflectionMatrix_perturbation_action]
    exact mul_le_mul_of_nonneg_right h (vecEuclideanNorm_nonneg v)

/-- Normalizing by the lower ellipticity constant changes the oscillation
from `δ` to `δ / (1 - δ)`, relative to the actual rescaled average. -/
theorem isMatrixPerturbationLE_normalized_radialReflectionMatrix_iff
    {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (ε : ℝ) (x : Vec d) :
    IsMatrixPerturbationLE ε
      ((1 - δ)⁻¹ • ((1 : Mat d) + δ • radialReflectionMatrix x))
      ((1 - δ)⁻¹ • (1 : Mat d)) ↔ δ / (1 - δ) ≤ ε := by
  rw [isMatrixPerturbationLE_smul_one_add_radialReflectionMatrix_iff hd]
  have hscale : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [abs_of_nonneg (mul_nonneg hscale hδ), div_eq_mul_inv, mul_comm]

/-- Adjoining unused identity directions preserves the normalized threshold
relative to the block coefficient's actual average. -/
theorem isMatrixPerturbationLE_matAppend_normalized_radialReflectionMatrix_iff
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Vec 2) :
    IsMatrixPerturbationLE ε
      (matAppend ((1 - δ)⁻¹ • ((1 : Mat 2) + δ • radialReflectionMatrix x))
        (1 : Mat n))
      (matAppend ((1 - δ)⁻¹ • (1 : Mat 2)) (1 : Mat n)) ↔
      δ / (1 - δ) ≤ ε := by
  exact (isMatrixPerturbationLE_matAppend_same_iff hε _ _ _).trans
    (isMatrixPerturbationLE_normalized_radialReflectionMatrix_iff
      (by norm_num) hδ hδ1 ε x)

end PDE
