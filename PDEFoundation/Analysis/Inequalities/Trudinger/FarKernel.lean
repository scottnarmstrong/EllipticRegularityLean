module

public import PDEFoundation.Analysis.Inequalities.Trudinger.Shells

/-!
# The far part of the Riesz kernel has logarithmic `L^{d'}` mass (Trudinger, Step 3)
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE
namespace Trudinger

variable {d : ℕ}

theorem far_term_eq {b : ℝ} (hb : 0 < b) : b ^ (-(d : ℝ)) * (2 * b) ^ d = 2 ^ d := by
  rw [Real.rpow_neg hb.le, Real.rpow_natCast, mul_pow]
  field_simp

/-- `∫_{(1/2)^k ≤ |x - y| < 2} |x - y|^{-d} dy ≤ (k+1) 2^d |B₁|`. -/
theorem lintegral_far_kernel_le (x : Vec d) (k : ℕ) :
    ∫⁻ y in {y : Vec d | (1 / 2 : ℝ) ^ k ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2},
        ENNReal.ofReal (vecEuclideanNorm (x - y) ^ (-(d : ℝ))) ≤
      ENNReal.ofReal ((k + 1) * 2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
  classical
  set ε : ℝ := (1 / 2 : ℝ) ^ k with hε
  have hεpos : 0 < ε := by positivity
  set b : ℕ → ℝ := fun j => 2 ^ j * ε with hb
  have hbpos : ∀ j, 0 < b j := fun j => by positivity
  have hpt : ∀ y ∈ {y : Vec d | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2},
      ENNReal.ofReal (vecEuclideanNorm (x - y) ^ (-(d : ℝ))) ≤
        ∑ j ∈ Finset.range (k + 1), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y := by
    rintro y ⟨hy1, hy2⟩
    have hrpos : 0 < vecEuclideanNorm (x - y) := lt_of_lt_of_le hεpos hy1
    have hP : ∃ j : ℕ, vecEuclideanNorm (x - y) < 2 ^ (j + 1) * ε := by
      refine ⟨k, ?_⟩
      have : (2 : ℝ) ^ (k + 1) * ε = 2 := by
        simp only [hε, pow_succ]
        rw [show (2 : ℝ) ^ k * 2 * (1 / 2) ^ k = 2 * (2 ^ k * (1 / 2) ^ k) by ring,
          ← mul_pow]
        norm_num
      rw [this]; exact hy2
    have hjk : Nat.find hP ≤ k := Nat.find_min' hP (by
      have : (2 : ℝ) ^ (k + 1) * ε = 2 := by
        simp only [hε, pow_succ]
        rw [show (2 : ℝ) ^ k * 2 * (1 / 2) ^ k = 2 * (2 ^ k * (1 / 2) ^ k) by ring,
          ← mul_pow]
        norm_num
      rw [this]; exact hy2)
    have hlt : vecEuclideanNorm (x - y) < 2 * b (Nat.find hP) := by
      have := Nat.find_spec hP
      simp only [hb]; rw [pow_succ] at this; linarith
    have hge : b (Nat.find hP) ≤ vecEuclideanNorm (x - y) := by
      rcases h : Nat.find hP with _ | j
      · simpa [hb] using hy1
      · have := Nat.find_min hP (m := j) (by omega)
        simp only [hb]; exact not_lt.mp this
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y) (fun _ _ => bot_le)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hjk)))
    rw [Set.indicator_of_mem ((mem_euclideanBall_iff_norm_sub_lt x y
      (by have := hbpos (Nat.find hP); positivity)).2 hlt)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (hbpos _) hge (by simp))
  calc _ ≤ ∫⁻ y in {y : Vec d | ε ≤ vecEuclideanNorm (x - y) ∧ vecEuclideanNorm (x - y) < 2},
        ∑ j ∈ Finset.range (k + 1), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y :=
        setLIntegral_mono' ((measurableSet_le measurable_const (measurable_norm_sub x)).inter
          (measurableSet_lt (measurable_norm_sub x) measurable_const)) hpt
    _ ≤ ∫⁻ y, ∑ j ∈ Finset.range (k + 1), (euclideanBall x (2 * b j)).indicator
          (fun _ => ENNReal.ofReal (b j ^ (-(d : ℝ)))) y := setLIntegral_le_lintegral _ _
    _ = ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (b j ^ (-(d : ℝ))) *
          volume (euclideanBall x (2 * b j)) := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_indicator_const (measurableSet_euclideanBall _ _)]
        · intro j _
          exact measurable_const.indicator (measurableSet_euclideanBall _ _)
    _ = ∑ j ∈ Finset.range (k + 1),
          ENNReal.ofReal (2 ^ d) * volume (euclideanBall (0 : Vec d) 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h2b : 0 < 2 * b j := by have := hbpos j; positivity
        rw [volume_euclideanBall_eq_unit_mul_of_pos x h2b, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), far_term_eq (hbpos j)]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 3
        push_cast; ring
