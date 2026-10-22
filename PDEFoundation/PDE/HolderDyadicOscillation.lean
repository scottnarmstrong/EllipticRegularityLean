module

public import PDEFoundation.PDE.HolderWeightedStep
public import PDEFoundation.Sobolev.H1.DyadicVectorMeans
public import PDEFoundation.Analysis.SchauderGradientBound

/-!
# Actual finite gradient Schauder iteration

The recurrences in this theorem are derived from the weak equation and exact
vector mean identities. The generic finite iteration is applied inside the
proof; none of its recurrence hypotheses is an additional PDE premise.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {d : ℕ}

/-- Uniform finite-depth gradient bounds for coefficients equal to the
identity, with the product `α(1-α)` as coefficient threshold. -/
theorem holder_dyadic_oscillation_bound [NeZero d]
    (hd : 2 ≤ d) {z : Vec d} {R α Ka KF : ℝ}
    (hR : 0 < R) (hα0 : 0 < α) (hα1 : α < 1)
    (hKa : 0 ≤ Ka) (hKF : 0 ≤ KF)
    {a : CoeffField d} {F : Vec d → Vec d}
    (ha : EuclideanMatrixHolderSeminormLE (euclideanBall z R) a α Ka)
    (hF : EuclideanFieldHolderSeminormLE (euclideanBall z R) F α KF)
    (ha0 : a z = 1) (u : H1Function (euclideanBall z R))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F)
    (hsmall : (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * Ka ≤
      α * (1 - α) / (32 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2)))) :
    ∀ n : ℕ,
      (R / dyadicRadius R n) ^ α *
          centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) u.grad ≤
        8 * (2 * Real.sqrt (integralAverage (euclideanBall z R)
          (fun x => vecNormSq (u.grad x))) +
            (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * KF / (1 - α)) ∧
      Real.sqrt (integralAverage (euclideanBall z (dyadicRadius R n))
          (fun x => vecNormSq (u.grad x))) ≤
        (40 * (1 + (2 : ℝ) ^ ((d : ℝ) / 2)) / α) *
          (2 * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
              (1 + 2 * (2 : ℝ) ^ ((d : ℝ) / 2)) * R ^ α * KF / (1 - α)) := by
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  let H : ℝ := 1 + 2 * D
  let E : ℕ → ℝ := fun n => (R / dyadicRadius R n) ^ α *
    centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) u.grad
  let m : ℕ → ℝ := fun n => vecEuclideanNorm
    (vectorIntegralAverage (euclideanBall z (dyadicRadius R n)) u.grad)
  let M : ℕ → ℝ := fun n => Real.sqrt
    (integralAverage (euclideanBall z (dyadicRadius R n)) (fun x => vecNormSq (u.grad x)))
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hH : 0 ≤ H := add_nonneg (by norm_num) (mul_nonneg (by norm_num) hD)
  have hrpow : 0 ≤ R ^ α := Real.rpow_nonneg hR.le _
  have hE0 : 0 ≤ E 0 := by
    dsimp only [E, centeredVectorMeanL2]
    exact mul_nonneg (Real.rpow_nonneg
      (div_nonneg hR.le (dyadicRadius_pos hR 0).le) _) (Real.sqrt_nonneg _)
  have hm0 : 0 ≤ m 0 := vecEuclideanNorm_nonneg _
  have hcancel (n : ℕ) : ((2 : ℝ) ^ (-α)) ^ n * E n =
      centeredVectorMeanL2 (euclideanBall z (dyadicRadius R n)) u.grad := by
    dsimp only [E]
    rw [← mul_assoc, two_rpow_neg_mul_div_dyadicRadius_rpow hR α n, one_mul]
  have hE (n : ℕ) : E (n + 1) ≤ (2 : ℝ) ^ (α - 1) * E n +
      (H * R ^ α * Ka) * M n + H * R ^ α * KF := by
    have hs := holder_weighted_dyadic_oscillation_step hd hR hα0 hα1 hKa hKF
      ha hF ha0 u hsol n
    change E (n + 1) ≤ (2 : ℝ) ^ (α - 1) * E n +
      H * R ^ α * (Ka * M n + KF) at hs
    exact hs.trans_eq (by ring)
  have hm (n : ℕ) : m (n + 1) ≤ m n +
      D * ((2 : ℝ) ^ (-α)) ^ n * E n := by
    rw [mul_assoc, hcancel]
    exact vecEuclideanNorm_vectorIntegralAverage_dyadic_succ_le hR u.gradMemL2 n
  have hM (n : ℕ) : M n ≤ m n + ((2 : ℝ) ^ (-α)) ^ n * E n := by
    rw [hcancel]
    exact sqrt_integralAverage_vecNormSq_dyadic_le_mean_add_centered hR u.gradMemL2 n
  have hinitE : E 0 ≤ M 0 := by
    have heq : E 0 = centeredVectorMeanL2 (euclideanBall z R) u.grad := by
      dsimp only [E]
      rw [dyadicRadius_zero, div_self hR.ne', Real.one_rpow, one_mul]
    rw [heq]
    simpa only [M, dyadicRadius_zero] using
      centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq_ball hR u.gradMemL2
  have hinitm : m 0 ≤ M 0 := by
    simpa only [m, M, dyadicRadius_zero] using
      vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq_ball
        hR u.gradMemL2
  have hsmall' : H * R ^ α * Ka ≤ α * (1 - α) / (32 * (1 + D)) := hsmall
  have hbound := schauderGradientIteration_explicit_bound hα0 hα1
    (mul_nonneg (mul_nonneg hH hrpow) hKa)
    (mul_nonneg (mul_nonneg hH hrpow) hKF) hD hE0 hm0 hE hm hM hsmall'
  have hbase : E 0 + m 0 + (H * R ^ α * KF) / (1 - α) ≤
      2 * M 0 + (H * R ^ α * KF) / (1 - α) := by
    linarith only [hinitE, hinitm]
  intro n
  have he := (hbound n).1.trans (mul_le_mul_of_nonneg_left hbase (by norm_num))
  have hm := (hbound n).2.trans (mul_le_mul_of_nonneg_left hbase
    (div_nonneg (mul_nonneg (by norm_num) (add_nonneg (by norm_num) hD)) hα0.le))
  simpa only [E, M, dyadicRadius_zero, D, H] using And.intro he hm

end PDE
