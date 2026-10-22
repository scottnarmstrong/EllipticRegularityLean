module

public import PDEFoundation.Ambient.CoefficientField

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Ellipticity algebra for the weighted energy estimate

The inverse-coercivity half of the project's nonsymmetric ellipticity
condition gives the sharp `Λ` coefficient in the Gaussian weight-gradient
term. This is the pointwise algebra behind the weighted energy inequality.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

/-- The cross term from a scalar spatial weight is absorbed by the principal
energy with residual coefficient exactly `Lam`. -/
theorem weightedEnergy_cross_term_bound {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (u : ℝ) (v p : Vec d) :
    -vecDot v (matVecMul A v) -
        2 * u * vecDot (matVecMul A v) p ≤
      Lam * vecNormSq p * u ^ 2 := by
  let Q : ℝ := vecDot v (matVecMul A v)
  let U : ℝ := vecEuclideanNorm (matVecMul A v)
  let V : ℝ := vecEuclideanNorm p
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have := hA.coercive v
    have hlam : 0 < lam := hA.lam_pos
    have hnorm : 0 ≤ vecNormSq v := vecNormSq_nonneg v
    nlinarith
  have hU2 : U ^ 2 ≤ Lam * Q := by
    dsimp [U, Q]
    rw [vecEuclideanNorm_sq]
    exact vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA v
  have hLam : 0 < Lam := hA.Lam_pos
  have hU : U ≤ Real.sqrt (Lam * Q) := Real.le_sqrt_of_sq_le hU2
  have hU0 : 0 ≤ U := vecEuclideanNorm_nonneg _
  have hV0 : 0 ≤ V := vecEuclideanNorm_nonneg p
  have hV2 : V ^ 2 = vecNormSq p := vecEuclideanNorm_sq p
  have hdot : |vecDot (matVecMul A v) p| ≤ U * V :=
    abs_vecDot_le_vecEuclideanNorm_mul _ _
  have hrootA : Real.sqrt (Lam * Q) = Real.sqrt Lam * Real.sqrt Q :=
    Real.sqrt_mul hLam.le Q
  have hb : 0 ≤ Real.sqrt Lam * |u| * V := by positivity
  have hdot' : |u * vecDot (matVecMul A v) p| ≤ Real.sqrt Q *
      (Real.sqrt Lam * |u| * V) := by
    calc
      |u * vecDot (matVecMul A v) p| =
          |u| * |vecDot (matVecMul A v) p| := abs_mul _ _
      _ ≤ |u| * (U * V) := mul_le_mul_of_nonneg_left hdot (abs_nonneg _)
      _ ≤ |u| * (Real.sqrt (Lam * Q) * V) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hU hV0) (abs_nonneg _)
      _ = Real.sqrt Q * (Real.sqrt Lam * |u| * V) := by
        rw [hrootA]
        ring
  have hYoung : 2 * Real.sqrt Q * (Real.sqrt Lam * |u| * V) ≤
      Q + (Real.sqrt Lam * |u| * V) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt Q - (Real.sqrt Lam * |u| * V)),
      Real.sq_sqrt hQ]
  have hQeq : vecDot v (matVecMul A v) = Q := rfl
  calc
    -vecDot v (matVecMul A v) -
        2 * u * vecDot (matVecMul A v) p = -Q -
          2 * u * vecDot (matVecMul A v) p := by rw [hQeq]
    _ ≤ -Q + 2 * |u * vecDot (matVecMul A v) p| := by
      have habs : -(u * vecDot (matVecMul A v) p) ≤
          |u * vecDot (matVecMul A v) p| := neg_le_abs _
      nlinarith
    _ ≤ -Q + 2 * Real.sqrt Q * (Real.sqrt Lam * |u| * V) := by
      nlinarith [hdot']
    _ ≤ (Real.sqrt Lam * |u| * V) ^ 2 := by nlinarith [hYoung]
    _ = Lam * vecNormSq p * u ^ 2 := by
      calc
        _ = Real.sqrt Lam ^ 2 * |u| ^ 2 * V ^ 2 := by ring
        _ = Lam * u ^ 2 * vecNormSq p := by
          rw [Real.sq_sqrt hLam.le, sq_abs, hV2]
        _ = Lam * vecNormSq p * u ^ 2 := by ring

end PDE.Parabolic.Cauchy.Weights
