module

public import PDEFoundation.Analysis.Inequalities.Trudinger.Normalized

/-!
# The Riesz potential of the gradient majorant is logarithmically bounded by its maximal function
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

theorem vecEuclideanNorm_sub_lt_two {x y : Vec d} (hx : x ∈ unitBall d) (hy : y ∈ unitBall d) :
    vecEuclideanNorm (x - y) < 2 := by
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hx
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hy
  rw [sub_zero] at hx' hy'
  have := vecEuclideanNorm_add_le x (-y)
  rw [vecEuclideanNorm_neg, ← sub_eq_add_neg] at this
  linarith

/-- The real Riesz potential of `G'` at a point of `B₁` where the maximal function of `G'/N` is at
most `m` is at most `N C₂ (log (2 + m))^{(d-1)/d}`. -/
theorem integral_riesz_le_log (hd : 2 ≤ d) {G' : Vec d → ℝ} (hG : Measurable G')
    (hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N)
    (hLd : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ))
    {x : Vec d} (hx : x ∈ unitBall d) {m : ℝ} (hm : 0 < m)
    (hM : uncenteredBallMaximal (fun y => (normalizedMajorant G' N y).toReal) x ≤
      ENNReal.ofReal m) :
    ∫ y in unitBall d, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * G' y ≤
      N * (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have hJ := lintegral_riesz_le_log hd x (measurable_normalizedMajorant hG N)
    (lintegral_normalizedMajorant_rpow hG hnn hN hd0 hLd)
    (fun y hy => vecEuclideanNorm_sub_lt_two hx (normalizedMajorant_ne_zero hy)) hm
    (lintegral_ball_normalizedMajorant_le hG hnn hN x hM)
  set K : Vec d → ℝ := fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) with hK
  have hKnn : ∀ y, 0 ≤ K y := fun y => Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
  have hKm : Measurable K := (measurable_norm_sub x).pow_const _
  have hB := measurableSet_euclideanBall (0 : Vec d) 1
  have hint : ∫ y in unitBall d, K y * G' y =
      (∫⁻ y in unitBall d, ENNReal.ofReal (K y * G' y)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y =>
      mul_nonneg (hKnn y) (hnn y)) (hKm.mul hG).aestronglyMeasurable
  have hlin : ∫⁻ y in unitBall d, ENNReal.ofReal (K y * G' y) =
      ENNReal.ofReal N * ∫⁻ y, ENNReal.ofReal (K y) * normalizedMajorant G' N y := by
    rw [← lintegral_const_mul (f := fun y => ENNReal.ofReal (K y) * normalizedMajorant G' N y) _
      ((ENNReal.measurable_ofReal.comp hKm).mul (measurable_normalizedMajorant hG N)),
      ← lintegral_indicator hB]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ unitBall d
    · simp only [normalizedMajorant, Set.indicator_of_mem hy]
      rw [← ENNReal.ofReal_mul (hKnn y), ← ENNReal.ofReal_mul hN.le]
      congr 1
      field_simp
    · simp [normalizedMajorant, hy]
  have hnonneg : 0 ≤ N * (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) := by
    have hlog : 0 ≤ Real.log (2 + m) := Real.log_nonneg (by linarith)
    have hu := unitVol_pos d
    unfold C2
    positivity
  change ∫ y in unitBall d, K y * G' y ≤ _
  rw [hint, hlin]
  refine ENNReal.toReal_le_of_le_ofReal hnonneg ?_
  calc ENNReal.ofReal N * ∫⁻ y, ENNReal.ofReal (K y) * normalizedMajorant G' N y
      ≤ ENNReal.ofReal N * ENNReal.ofReal (C2 d * Real.log (2 + m) ^ (((d : ℝ) - 1) / d)) :=
        mul_le_mul' le_rfl hJ
    _ = _ := (ENNReal.ofReal_mul hN.le).symm
