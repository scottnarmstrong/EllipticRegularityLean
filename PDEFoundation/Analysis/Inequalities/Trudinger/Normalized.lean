module

public import PDEFoundation.Analysis.Inequalities.Trudinger.PointwiseLog
public import PDEFoundation.Measure.BallMaximalWeak

/-!
# The normalized gradient majorant and its maximal function (Trudinger, Steps 1-4 for `g / N`)

For a measurable `G' ≥ 0` on the unit ball with `‖G'‖_{L^d(B₁)} = N > 0`, the function
`f = 1_{B₁} G' / N` has `‖f‖_{L^d} = 1`; its uncentered maximal function controls the Riesz
potential of `G'` through the pointwise logarithmic bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

/-- The unit ball. -/
abbrev unitBall (d : ℕ) : Set (Vec d) := euclideanBall (0 : Vec d) 1

/-- The normalized majorant `1_{B₁} G' / N`. -/
noncomputable def normalizedMajorant (G' : Vec d → ℝ) (N : ℝ) : Vec d → ℝ≥0∞ :=
  (unitBall d).indicator fun y => ENNReal.ofReal (G' y / N)

theorem measurable_normalizedMajorant {G' : Vec d → ℝ} (hG : Measurable G') (N : ℝ) :
    Measurable (normalizedMajorant G' N) :=
  (ENNReal.measurable_ofReal.comp (hG.div_const N)).indicator (measurableSet_euclideanBall _ _)

theorem normalizedMajorant_ne_top (G' : Vec d → ℝ) (N : ℝ) (y : Vec d) :
    normalizedMajorant G' N y ≠ ⊤ := by
  unfold normalizedMajorant
  by_cases hy : y ∈ unitBall d <;> simp [Set.indicator_of_mem, hy]

theorem normalizedMajorant_ne_zero {G' : Vec d → ℝ} {N : ℝ} {y : Vec d}
    (h : normalizedMajorant G' N y ≠ 0) : y ∈ unitBall d := by
  by_contra hy
  simp [normalizedMajorant, hy] at h

theorem lintegral_normalizedMajorant_rpow {G' : Vec d → ℝ} (hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N) (hd : 0 < (d : ℝ))
    (hLd : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ^ (d : ℝ) = ENNReal.ofReal N ^ (d : ℝ)) :
    ∫⁻ y, normalizedMajorant G' N y ^ (d : ℝ) ≤ 1 := by
  have h1 : ∫⁻ y, normalizedMajorant G' N y ^ (d : ℝ) =
      ∫⁻ y in unitBall d, ENNReal.ofReal (G' y / N) ^ (d : ℝ) := by
    rw [← lintegral_indicator (measurableSet_euclideanBall _ _)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ unitBall d
    · simp [normalizedMajorant, hy]
    · have hd0 : d ≠ 0 := by exact_mod_cast hd.ne'
      simp [normalizedMajorant, hy, hd0]
  rw [h1]
  have h2 : ∀ y, ENNReal.ofReal (G' y / N) ^ (d : ℝ) =
      ENNReal.ofReal (1 / N) ^ (d : ℝ) * ENNReal.ofReal (G' y) ^ (d : ℝ) := fun y => by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd.le, ← ENNReal.ofReal_mul (by positivity),
      one_div, inv_mul_eq_div]
  simp_rw [h2]
  rw [lintegral_const_mul (f := fun y => ENNReal.ofReal (G' y) ^ (d : ℝ)) _
    ((ENNReal.measurable_ofReal.comp hG).pow_const _), hLd,
    ← ENNReal.mul_rpow_of_nonneg _ _ hd.le, ← ENNReal.ofReal_mul (by positivity)]
  simp [hN.ne', one_div]

theorem lintegral_normalizedMajorant_le {G' : Vec d → ℝ} (hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (hN : 0 < N) (θ : ℝ)
    (hL1 : ∫⁻ y in unitBall d, ENNReal.ofReal (G' y) ≤
      ENNReal.ofReal N * volume (unitBall d) ^ θ) :
    ∫⁻ y, normalizedMajorant G' N y ≤ volume (unitBall d) ^ θ := by
  have h1 : ∫⁻ y, normalizedMajorant G' N y =
      ∫⁻ y in unitBall d, ENNReal.ofReal (G' y / N) := by
    rw [← lintegral_indicator (measurableSet_euclideanBall _ _)]
    rfl
  rw [h1]
  have h2 : ∀ y, ENNReal.ofReal (G' y / N) = ENNReal.ofReal (1 / N) * ENNReal.ofReal (G' y) :=
    fun y => by
      rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_eq_div]
  simp_rw [h2]
  rw [lintegral_const_mul (f := fun y => ENNReal.ofReal (G' y)) _
    (ENNReal.measurable_ofReal.comp hG)]
  calc _ ≤ ENNReal.ofReal (1 / N) * (ENNReal.ofReal N * volume (unitBall d) ^ θ) :=
        mul_le_mul' le_rfl hL1
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        simp [hN.ne']

/-- Averages of the normalized majorant over balls centered at a point where the maximal
function is at most `m` are at most `m`. -/
theorem lintegral_ball_normalizedMajorant_le {G' : Vec d → ℝ} (_hG : Measurable G')
    (_hnn : ∀ y, 0 ≤ G' y) {N : ℝ} (_hN : 0 < N) {m : ℝ} (x : Vec d)
    (hM : uncenteredBallMaximal (fun y => (normalizedMajorant G' N y).toReal) x ≤
      ENNReal.ofReal m) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫⁻ y in euclideanBall x ρ, normalizedMajorant G' N y ≤
      ENNReal.ofReal m * volume (euclideanBall x ρ) := by
  have hx : x ∈ euclideanBall x ρ := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hρ]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hρ
  have h := (lintegralAverage_le_uncenteredBallMaximal
    (fun y => (normalizedMajorant G' N y).toReal) hρ hx).trans hM
  have hfb : ∀ y, ENNReal.ofReal |(normalizedMajorant G' N y).toReal| =
      normalizedMajorant G' N y := fun y => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (normalizedMajorant_ne_top _ _ _)]
  simp_rw [hfb] at h
  have hpos := volume_euclideanBall_pos x hρ
  have hfin := volume_euclideanBall_ne_top x hρ.le
  calc _ = volume (euclideanBall x ρ) *
        ((volume (euclideanBall x ρ))⁻¹ * ∫⁻ y in euclideanBall x ρ, normalizedMajorant G' N y) := by
        rw [ENNReal.mul_inv_cancel_left hpos.ne' hfin]
    _ ≤ volume (euclideanBall x ρ) * ENNReal.ofReal m := mul_le_mul_right h _
    _ = _ := mul_comm _ _
