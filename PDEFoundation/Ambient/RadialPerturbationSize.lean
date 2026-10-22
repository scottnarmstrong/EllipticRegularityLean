module

public import PDEFoundation.Ambient.PlanarRadialProjection
public import PDEFoundation.Ambient.Basis

@[expose] public section

namespace PDE

/-- The radial reflection perturbation has exactly the stated Euclidean
operator action on every vector. -/
theorem vecEuclideanNorm_radialReflectionMatrix_perturbation_action
    {d : ℕ} (δ : ℝ) (x v : Vec d) :
    vecEuclideanNorm (matVecMul
      (((1 : Mat d) + δ • radialReflectionMatrix x) - 1) v) =
      |δ| * vecEuclideanNorm v := by
  have haction : matVecMul
      (((1 : Mat d) + δ • radialReflectionMatrix x) - 1) v =
      δ • matVecMul (radialReflectionMatrix x) v := by
    change ((1 + δ • radialReflectionMatrix x) - 1).mulVec v = _
    rw [show (1 + δ • radialReflectionMatrix x) - 1 =
      δ • radialReflectionMatrix x by abel]
    exact Matrix.smul_mulVec δ _ _
  rw [haction, vecEuclideanNorm_smul,
    vecEuclideanNorm_matVecMul_radialReflectionMatrix]

/-- In positive dimension, the exact perturbation size is `|δ|`; testing a
coordinate vector supplies necessity as well as sufficiency. -/
theorem isMatrixPerturbationLE_one_add_radialReflectionMatrix_iff
    {d : ℕ} (hd : 0 < d) (δ ε : ℝ) (x : Vec d) :
    IsMatrixPerturbationLE ε
      ((1 : Mat d) + δ • radialReflectionMatrix x) (1 : Mat d) ↔ |δ| ≤ ε := by
  constructor
  · intro h
    have hk := h (basisVec ⟨0, hd⟩)
    rw [vecEuclideanNorm_radialReflectionMatrix_perturbation_action,
      vecEuclideanNorm_basisVec, mul_one, mul_one] at hk
    exact hk
  · intro h v
    rw [vecEuclideanNorm_radialReflectionMatrix_perturbation_action]
    exact mul_le_mul_of_nonneg_right h (vecEuclideanNorm_nonneg v)

end PDE
