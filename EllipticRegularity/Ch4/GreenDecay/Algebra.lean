module

public import PDEFoundation.Sobolev.H1.Pairing
public import PDEFoundation.Sobolev.H1.GraphPairing
public import PDEFoundation.Ambient.CoefficientField

/-!
# Elementary algebra of `vecDot` and `matVecMul`, and `L²`-norm bookkeeping

Small public lemmas used throughout the Green decay development.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

@[simp] theorem vecDot_zero_left' (y : Vec d) : vecDot (0 : Vec d) y = 0 := by
  simp [vecDot]

@[simp] theorem vecDot_zero_right' (y : Vec d) : vecDot y (0 : Vec d) = 0 := by
  simp [vecDot]

theorem vecDot_smul_left' (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem vecDot_sub_left' (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem vecDot_sub_right' (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem matVecMul_smul_left' (c : ℝ) (A : Mat d) (x : Vec d) :
    matVecMul (c • A) x = c • matVecMul A x := by
  change (c • A).mulVec x = c • A.mulVec x
  rw [Matrix.smul_mulVec]

theorem matVecMul_sub_right' (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  change A.mulVec (x - y) = A.mulVec x - A.mulVec y
  rw [Matrix.mulVec_sub]

theorem vecEuclideanNorm_sq' (x : Vec d) : vecEuclideanNorm x ^ 2 = vecNormSq x := by
  unfold vecEuclideanNorm
  exact Real.sq_sqrt (vecNormSq_nonneg x)

theorem vecDot_matVecMul_transpose'' (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  simp only [vecDot, matVecMul, matTranspose, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem abs_vecDot_le_mul_norm' (x y : Vec d) :
    |vecDot x y| ≤ vecEuclideanNorm x * vecEuclideanNorm y := by
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _))
  rw [mul_pow, vecEuclideanNorm_sq', vecEuclideanNorm_sq']
  exact sq_vecDot_le_vecNormSq_mul_vecNormSq x y

/-- `‖f‖_{L²(U)}² = ∫_U f²` for an `L²` function, with the extended norm converted to a real. -/
theorem toReal_eLpNorm_sq {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemL2On U f) :
    (eLpNorm f 2 (volumeOn U)).toReal ^ 2 = ∫ x in U, f x ^ 2 := by
  have h := integral_sq_eq_sq_norm_of_ae_eq hf.toScalarLp f hf.coeFn_toScalarLp
  rw [show (∫ x in U, f x ^ 2) = ∫ x, f x ^ 2 ∂(volumeOn U) from rfl, h]
  congr 1
  exact (Lp.norm_toLp f hf).symm

end

end PDE.Ch4GreenDecay
