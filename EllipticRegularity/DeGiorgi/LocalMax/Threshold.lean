module

public import EllipticRegularity.DeGiorgi.LevelSetRecurrence
public import PDEFoundation.Analysis.NonlinearIteration

/-!
# The smallness threshold of the De Giorgi iteration

This module contains the scalar computation showing that, for the coefficient
`deGiorgiBallIterationCoefficient d 1 Λ (1/2) 1 K` of the nested-ball
recurrence, the smallness threshold of the nonlinear iteration is bounded
below by an explicit multiple of `K ^ 2 * (10 * Λ) ^ (-d / 2)`.  This is the
computation that produces the exponent `Λ ^ (d / 4)` in the `L^∞` estimate.
-/

@[expose] public section

namespace PDE.DGNMLocalMax

open PDE

/-- The dimensional constant in the smallness threshold. -/
noncomputable def thresholdConst (d : ℕ) : ℝ :=
  (((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 * 4096 * deGiorgiBallIterationBase d) ^
      (-((d : ℝ) / 2))) *
    deGiorgiBallIterationBase d ^ (-(1 / deGiorgiBallIterationBeta d ^ 2))

theorem thresholdConst_pos (d : ℕ) : 0 < thresholdConst d := by
  have hS : (0 : ℝ) < zeroBoundarySobolevConstantTwo d := by
    exact_mod_cast zeroBoundarySobolevConstantTwo_pos d
  have hB : 0 < deGiorgiBallIterationBase d :=
    lt_trans one_pos (deGiorgiBallIterationBase_one_lt d)
  unfold thresholdConst
  positivity

/-- The threshold of the nonlinear iteration for the unit-to-half-ball recurrence
dominates `thresholdConst d * K ^ 2 * (10 * Λ) ^ (-d / 2)`. -/
theorem threshold_le {d : ℕ} (hd : 3 ≤ d) {Λ K : ℝ} (hΛ : 1 ≤ Λ) (hK : 0 < K) :
    thresholdConst d * K ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2)) ≤
      deGiorgiBallIterationCoefficient d 1 Λ (1 / 2) 1 K ^
          (-(1 / deGiorgiBallIterationBeta d)) *
        deGiorgiBallIterationBase d ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hS : (0 : ℝ) < zeroBoundarySobolevConstantTwo d := by
    exact_mod_cast zeroBoundarySobolevConstantTwo_pos d
  have hB : 0 < deGiorgiBallIterationBase d :=
    lt_trans one_pos (deGiorgiBallIterationBase_one_lt d)
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hβ : 1 / deGiorgiBallIterationBeta d = (d : ℝ) / 2 := by
    unfold deGiorgiBallIterationBeta
    field_simp
  set S : ℝ := (zeroBoundarySobolevConstantTwo d : ℝ) with hSdef
  set B : ℝ := deGiorgiBallIterationBase d with hBdef
  -- rewrite the coefficient
  have hcoef : deGiorgiBallIterationCoefficient d 1 Λ (1 / 2) 1 K =
      (S ^ 2 * (8 * Λ + 2) * 4096 * B) * K ^ (-(4 / (d : ℝ))) := by
    unfold deGiorgiBallIterationCoefficient
    rw [← hSdef, ← hBdef]
    norm_num
    ring
  rw [hcoef, hβ]
  have hP : 0 < S ^ 2 * (8 * Λ + 2) * 4096 * B := by positivity
  have hKp : 0 < K ^ (-(4 / (d : ℝ))) := Real.rpow_pos_of_pos hK _
  rw [Real.mul_rpow hP.le hKp.le]
  have hK2 : (K ^ (-(4 / (d : ℝ)))) ^ (-((d : ℝ) / 2)) = K ^ 2 := by
    rw [← Real.rpow_mul hK.le]
    have : (-(4 / (d : ℝ))) * (-((d : ℝ) / 2)) = ((2 : ℕ) : ℝ) := by
      field_simp
      norm_num
    rw [this, Real.rpow_natCast]
  rw [hK2]
  have hmono : (S ^ 2 * (10 * Λ) * 4096 * B) ^ (-((d : ℝ) / 2)) ≤
      (S ^ 2 * (8 * Λ + 2) * 4096 * B) ^ (-((d : ℝ) / 2)) := by
    apply Real.rpow_le_rpow_of_nonpos hP
    · have : 0 ≤ S ^ 2 * 4096 * B := by positivity
      nlinarith
    · have : 0 ≤ (d : ℝ) / 2 := by positivity
      linarith
  have hsplit : (S ^ 2 * (10 * Λ) * 4096 * B) ^ (-((d : ℝ) / 2)) =
      (S ^ 2 * 4096 * B) ^ (-((d : ℝ) / 2)) * (10 * Λ) ^ (-((d : ℝ) / 2)) := by
    rw [show S ^ 2 * (10 * Λ) * 4096 * B = (S ^ 2 * 4096 * B) * (10 * Λ) by ring]
    exact Real.mul_rpow (by positivity) (by positivity)
  unfold thresholdConst
  rw [← hSdef, ← hBdef]
  have hBp : 0 ≤ B ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) := by positivity
  calc (S ^ 2 * 4096 * B) ^ (-((d : ℝ) / 2)) *
        B ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) * K ^ 2 * (10 * Λ) ^ (-((d : ℝ) / 2))
      = ((S ^ 2 * 4096 * B) ^ (-((d : ℝ) / 2)) * (10 * Λ) ^ (-((d : ℝ) / 2))) * K ^ 2 *
          B ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) := by ring
    _ = (S ^ 2 * (10 * Λ) * 4096 * B) ^ (-((d : ℝ) / 2)) * K ^ 2 *
          B ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) := by rw [hsplit]
    _ ≤ (S ^ 2 * (8 * Λ + 2) * 4096 * B) ^ (-((d : ℝ) / 2)) * K ^ 2 *
          B ^ (-(1 / deGiorgiBallIterationBeta d ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ hBp
        exact mul_le_mul_of_nonneg_right hmono (sq_nonneg K)

end PDE.DGNMLocalMax
