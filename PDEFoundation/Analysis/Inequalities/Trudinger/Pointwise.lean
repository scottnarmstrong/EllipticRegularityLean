module

public import PDEFoundation.Analysis.Inequalities.Trudinger.FarKernel

/-!
# The pointwise logarithmic Riesz bound (Trudinger, Steps 2-4)

If `‖f‖_{L^d} ≤ 1`, `f` is supported at distance `< 2` from `x`, and all ball averages of `f`
around `x` are at most `m`, then the Riesz potential of `f` at `x` is at most
`C₂ (log (2 + m))^{(d-1)/d}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

theorem kernel_rpow_conj (hd : 2 ≤ d) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ ((1 : ℝ) - d)) ^ ((d : ℝ) / ((d : ℝ) - 1)) =
      ENNReal.ofReal (r ^ (-(d : ℝ))) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hr _) (by
    have : (0 : ℝ) < d - 1 := by linarith
    positivity), ← Real.rpow_mul hr]
  congr 2
  field_simp
  ring

/-- Far part of the Riesz potential (Trudinger, Step 3), via Hölder and the shell estimate. -/
theorem lintegral_far_le (hd : 2 ≤ d) (x : Vec d) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hLd : ∫⁻ y, f y ^ (d : ℝ) ≤ 1) (k : ℕ) :
    ∫⁻ y in {y : Vec d | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2},
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y ≤
      (ENNReal.ofReal ((k + 1) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1)) ^
        (((d : ℝ) - 1) / d) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set S : Set (Vec d) :=
    {y | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2} with hS
  have hpq : (d : ℝ).HolderConjugate ((d : ℝ) / ((d : ℝ) - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl
  have hK : Measurable fun y : Vec d =>
      ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) :=
    ENNReal.measurable_ofReal.comp ((measurable_norm_sub x).pow_const _)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict S) hpq hf.aemeasurable
    hK.aemeasurable
  have h1 : ∫⁻ y in S, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) * f y =
      ∫⁻ y in S, f y * ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) :=
    lintegral_congr fun y => mul_comm _ _
  rw [h1]
  refine le_trans (le_of_eq rfl) (hH.trans ?_)
  have hA : (∫⁻ y in S, f y ^ (d : ℝ)) ^ (1 / (d : ℝ)) ≤ 1 := by
    calc (∫⁻ y in S, f y ^ (d : ℝ)) ^ (1 / (d : ℝ)) ≤ 1 ^ (1 / (d : ℝ)) :=
          ENNReal.rpow_le_rpow ((setLIntegral_le_lintegral _ _).trans hLd) (by positivity)
      _ = 1 := ENNReal.one_rpow _
  have hB : ∫⁻ y in S, (ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d))) ^
      ((d : ℝ) / ((d : ℝ) - 1)) ≤
      ENNReal.ofReal ((k + 1) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (lintegral_far_kernel_le x k)
    exact kernel_rpow_conj hd (vecEuclideanNorm_nonneg _)
  have hB' := ENNReal.rpow_le_rpow hB (z := 1 / ((d : ℝ) / ((d : ℝ) - 1))) (by
    have : (0 : ℝ) < d - 1 := by linarith
    positivity)
  rw [one_div_div] at hB'
  rw [one_div_div]
  refine (mul_le_mul_left hA _).trans ?_
  rw [one_mul]
  exact hB'
