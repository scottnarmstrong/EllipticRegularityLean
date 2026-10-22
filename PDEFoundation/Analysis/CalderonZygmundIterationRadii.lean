module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Radii for the perturbative Calderón--Zygmund iteration -/

@[expose] public section

namespace PDE

/-- The dimension-dependent ratio used by the local Calderón--Zygmund iteration. -/
noncomputable def calderonZygmundIterationSigma (d : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(1 : ℝ) / (d : ℝ))

/-- The increasing sequence of normalized interior radii. -/
noncomputable def calderonZygmundIterationRadius (d j : ℕ) : ℝ :=
  3 / 4 - calderonZygmundIterationSigma d ^ j / 4

/-- The iteration ratio is positive in every dimension. -/
lemma calderonZygmundIterationSigma_pos {d : ℕ} :
    0 < calderonZygmundIterationSigma d := by
  unfold calderonZygmundIterationSigma
  positivity

/-- In positive dimension, the iteration ratio is strictly below one. -/
lemma calderonZygmundIterationSigma_lt_one {d : ℕ} (hd : 0 < d) :
    calderonZygmundIterationSigma d < 1 := by
  unfold calderonZygmundIterationSigma
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

/-- The first normalized radius is one half. -/
@[simp] lemma calderonZygmundIterationRadius_zero (d : ℕ) :
    calderonZygmundIterationRadius d 0 = 1 / 2 := by
  unfold calderonZygmundIterationRadius
  norm_num

/-- Every radius lies in the half-open interval from one half to three quarters. -/
lemma calderonZygmundIterationRadius_mem {d j : ℕ} (hd : 0 < d) :
    1 / 2 ≤ calderonZygmundIterationRadius d j ∧
      calderonZygmundIterationRadius d j < 3 / 4 := by
  have hs0 := calderonZygmundIterationSigma_pos (d := d)
  have hs1 := calderonZygmundIterationSigma_lt_one hd
  have hp0 : 0 < calderonZygmundIterationSigma d ^ j := pow_pos hs0 _
  have hp1 : calderonZygmundIterationSigma d ^ j ≤ 1 := pow_le_one₀ hs0.le hs1.le
  unfold calderonZygmundIterationRadius
  constructor <;> nlinarith

/-- Consecutive normalized radii are strictly increasing. -/
lemma calderonZygmundIterationRadius_strictMono {d j : ℕ} (hd : 0 < d) :
    calderonZygmundIterationRadius d j < calderonZygmundIterationRadius d (j + 1) := by
  have hs0 := calderonZygmundIterationSigma_pos (d := d)
  have hs1 := calderonZygmundIterationSigma_lt_one hd
  have hp0 : 0 < calderonZygmundIterationSigma d ^ j := pow_pos hs0 _
  rw [calderonZygmundIterationRadius, calderonZygmundIterationRadius, pow_succ]
  nlinarith

/-- Exact formula for the gap between consecutive radii. -/
lemma calderonZygmundIterationRadius_gap (d j : ℕ) :
    calderonZygmundIterationRadius d (j + 1) -
        calderonZygmundIterationRadius d j =
      (1 - calderonZygmundIterationSigma d) *
        calderonZygmundIterationSigma d ^ j / 4 := by
  unfold calderonZygmundIterationRadius
  rw [pow_succ]
  ring

/-- Raising the ratio to negative half the dimension gives `sqrt 2`. -/
lemma calderonZygmundIterationSigma_rpow_neg_half {d : ℕ} (hd : 0 < d) :
    calderonZygmundIterationSigma d ^ (-(d : ℝ) / 2) = Real.sqrt 2 := by
  unfold calderonZygmundIterationSigma
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_eq_rpow]
  congr 1
  field_simp

/-- Exact inverse dimensional power of a consecutive-radius gap. -/
lemma calderonZygmundIterationRadius_gap_rpow {d j : ℕ} (hd : 0 < d) :
    (calderonZygmundIterationRadius d (j + 1) -
          calderonZygmundIterationRadius d j) ^ (-(d : ℝ) / 2) =
      (4 / (1 - calderonZygmundIterationSigma d)) ^ ((d : ℝ) / 2) *
        (Real.sqrt 2) ^ j := by
  have hs0 := calderonZygmundIterationSigma_pos (d := d)
  have hs1 := calderonZygmundIterationSigma_lt_one hd
  have hsub0 : 0 < 1 - calderonZygmundIterationSigma d := sub_pos.mpr hs1
  have hbase0 : 0 ≤ (1 - calderonZygmundIterationSigma d) / 4 :=
    (div_pos hsub0 (by norm_num)).le
  rw [calderonZygmundIterationRadius_gap]
  rw [show (1 - calderonZygmundIterationSigma d) *
      calderonZygmundIterationSigma d ^ j / 4 =
      ((1 - calderonZygmundIterationSigma d) / 4) *
        calderonZygmundIterationSigma d ^ j by ring]
  rw [Real.mul_rpow hbase0 (pow_nonneg hs0.le _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
  rw [show ((j : ℝ) * (-(d : ℝ) / 2)) =
      (-(d : ℝ) / 2) * j by ring]
  rw [Real.rpow_mul hs0.le]
  rw [calderonZygmundIterationSigma_rpow_neg_half hd, Real.rpow_natCast]
  congr 1
  rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring]
  rw [Real.rpow_neg hbase0, ← Real.inv_rpow hbase0]
  congr 2
  field_simp
