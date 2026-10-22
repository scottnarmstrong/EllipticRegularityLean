module

public import PDEFoundation.Ambient.Matrix

/-!
# Euclidean matrix perturbation bounds

This module records the native-vector operator bound for a matrix difference
and derives its pointwise bilinear and identity-coercivity consequences.
-/

@[expose] public section

namespace PDE

/-- `A` is within Euclidean operator distance `delta` of `B`, stated directly
on the shared native vector carrier. -/
def IsMatrixPerturbationLE {d : ℕ} (delta : ℝ) (A B : Mat d) : Prop :=
  ∀ xi : Vec d,
    vecEuclideanNorm (matVecMul (A - B) xi) ≤ delta * vecEuclideanNorm xi

private theorem matVecMul_sub {d : ℕ} (A B : Mat d) (xi : Vec d) :
    matVecMul (A - B) xi = matVecMul A xi - matVecMul B xi := by
  classical
  change (A - B).mulVec xi = A.mulVec xi - B.mulVec xi
  rw [Matrix.sub_mulVec]

private theorem matVecMul_one {d : ℕ} (xi : Vec d) :
    matVecMul (1 : Mat d) xi = xi := by
  classical
  change (1 : Mat d).mulVec xi = xi
  exact Matrix.one_mulVec xi

private theorem matVecMul_eq_add_sub_one {d : ℕ} (A : Mat d) (xi : Vec d) :
    matVecMul A xi = xi + matVecMul (A - 1) xi := by
  have hsub : matVecMul (A - 1) xi = matVecMul A xi - xi := by
    rw [matVecMul_sub, matVecMul_one]
  rw [hsub]
  abel

private theorem vecDot_add_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp only [vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The perturbation controls the absolute mixed term, with no symmetry
assumption on either matrix. -/
theorem abs_vecDot_matVecMul_sub_le_of_isMatrixPerturbationLE
    {d : ℕ} {delta : ℝ} {A B : Mat d}
    (hAB : IsMatrixPerturbationLE delta A B)
    (eta xi : Vec d) :
    |vecDot eta (matVecMul (A - B) xi)| ≤
      delta * (vecEuclideanNorm eta * vecEuclideanNorm xi) := by
  calc
    |vecDot eta (matVecMul (A - B) xi)| ≤
        vecEuclideanNorm eta * vecEuclideanNorm (matVecMul (A - B) xi) :=
      abs_vecDot_le_vecEuclideanNorm_mul eta _
    _ ≤ vecEuclideanNorm eta * (delta * vecEuclideanNorm xi) :=
      mul_le_mul_of_nonneg_left (hAB xi) (vecEuclideanNorm_nonneg eta)
    _ = delta * (vecEuclideanNorm eta * vecEuclideanNorm xi) := by ring

/-- If `A` is within `delta` of the identity, its quadratic form is bounded
below by `(1 - delta)` times the Euclidean square. -/
theorem one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
    {d : ℕ} {delta : ℝ} {A : Mat d}
    (hA : IsMatrixPerturbationLE delta A (1 : Mat d))
    (xi : Vec d) :
    (1 - delta) * vecNormSq xi ≤ vecDot xi (matVecMul A xi) := by
  have hdev :=
    abs_vecDot_matVecMul_sub_le_of_isMatrixPerturbationLE hA xi xi
  have hnormsq : vecEuclideanNorm xi * vecEuclideanNorm xi = vecNormSq xi := by
    nlinarith [vecEuclideanNorm_sq xi]
  rw [hnormsq] at hdev
  have hlow : -(delta * vecNormSq xi) ≤
      vecDot xi (matVecMul (A - 1) xi) := by
    exact neg_le_of_abs_le hdev
  have hsplit : vecDot xi (matVecMul A xi) =
      vecNormSq xi + vecDot xi (matVecMul (A - 1) xi) := by
    rw [matVecMul_eq_add_sub_one, vecDot_add_right, vecNormSq]
  rw [hsplit]
  nlinarith only [hlow]

/-- The identity perturbation bound also controls the full matrix action by
`1 + delta` in Euclidean norm. -/
theorem vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE
    {d : ℕ} {delta : ℝ} {A : Mat d}
    (hA : IsMatrixPerturbationLE delta A (1 : Mat d))
    (xi : Vec d) :
    vecEuclideanNorm (matVecMul A xi) ≤
      (1 + delta) * vecEuclideanNorm xi := by
  have hdev := hA xi
  rw [matVecMul_eq_add_sub_one]
  calc
    vecEuclideanNorm (xi + matVecMul (A - 1) xi) ≤
        vecEuclideanNorm xi + vecEuclideanNorm (matVecMul (A - 1) xi) :=
      vecEuclideanNorm_add_le xi _
    _ ≤ vecEuclideanNorm xi + delta * vecEuclideanNorm xi :=
      by nlinarith only [hdev]
    _ = (1 + delta) * vecEuclideanNorm xi := by ring

/-- The identity perturbation bound gives the matching absolute quadratic
upper bound. -/
theorem abs_vecDot_matVecMul_le_one_add_delta_mul_vecNormSq_of_isMatrixPerturbationLE
    {d : ℕ} {delta : ℝ} {A : Mat d}
    (hA : IsMatrixPerturbationLE delta A (1 : Mat d))
    (xi : Vec d) :
    |vecDot xi (matVecMul A xi)| ≤ (1 + delta) * vecNormSq xi := by
  have hnorm :=
    vecEuclideanNorm_matVecMul_le_one_add_delta_mul_of_isMatrixPerturbationLE
      hA xi
  have hnormsq : vecEuclideanNorm xi * vecEuclideanNorm xi = vecNormSq xi := by
    nlinarith [vecEuclideanNorm_sq xi]
  calc
    |vecDot xi (matVecMul A xi)| ≤
        vecEuclideanNorm xi * vecEuclideanNorm (matVecMul A xi) :=
      abs_vecDot_le_vecEuclideanNorm_mul xi _
    _ ≤ vecEuclideanNorm xi *
        ((1 + delta) * vecEuclideanNorm xi) :=
      mul_le_mul_of_nonneg_left hnorm (vecEuclideanNorm_nonneg xi)
    _ = (1 + delta) * (vecEuclideanNorm xi * vecEuclideanNorm xi) := by
      ring
    _ = (1 + delta) * vecNormSq xi := by
      rw [hnormsq]

end PDE
