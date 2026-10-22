module

public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Nested De Giorgi scales

This module records the explicit radii and truncation levels used in the
standard nested-ball De Giorgi iteration.

## Main definitions

- `deGiorgiRadius r R n` is the radius between `r` and `R` at step `n`.
- `deGiorgiLevel K n` is the truncation level between `0` and `K` at step `n`.

## Main results

- exact formulas for successive gaps;
- monotonicity, positivity, and limiting values;
- nesting of the associated round balls.

The powers use real exponents throughout. This matches the quantitative
iteration convention used by the related local developments.
-/

@[expose] public section

namespace PDE

open Filter Topology

/-- The nested radii `r + (R - r) 2^{-n}` of the De Giorgi iteration. -/
noncomputable def deGiorgiRadius (r R : ℝ) (n : ℕ) : ℝ :=
  r + (R - r) * (2 : ℝ) ^ (-(n : ℝ))

/-- The nested levels `K (1 - 2^{-n})` of the De Giorgi iteration. -/
noncomputable def deGiorgiLevel (K : ℝ) (n : ℕ) : ℝ :=
  K * (1 - (2 : ℝ) ^ (-(n : ℝ)))

private theorem two_rpow_neg_succ (n : ℕ) :
    (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ (-(n : ℝ)) / 2 := by
  rw [show (-((n + 1 : ℕ) : ℝ)) = -(n : ℝ) + (-1 : ℝ) by
    push_cast
    ring]
  rw [Real.rpow_add (by norm_num), Real.rpow_neg_one]
  ring

@[simp]
theorem deGiorgiRadius_zero (r R : ℝ) : deGiorgiRadius r R 0 = R := by
  simp [deGiorgiRadius]

@[simp]
theorem deGiorgiLevel_zero (K : ℝ) : deGiorgiLevel K 0 = 0 := by
  simp [deGiorgiLevel]

/-- The radius gap at one De Giorgi step. -/
theorem deGiorgiRadius_sub_succ (r R : ℝ) (n : ℕ) :
    deGiorgiRadius r R n - deGiorgiRadius r R (n + 1) =
      (R - r) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) := by
  rw [deGiorgiRadius, deGiorgiRadius, two_rpow_neg_succ]
  ring

/-- The level gap at one De Giorgi step. -/
theorem deGiorgiLevel_succ_sub (K : ℝ) (n : ℕ) :
    deGiorgiLevel K (n + 1) - deGiorgiLevel K n =
      K * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) := by
  rw [deGiorgiLevel, deGiorgiLevel, two_rpow_neg_succ]
  ring

/-- The exact conversion from a real power of four to a real power of two. -/
theorem four_rpow_eq (y : ℝ) :
    (4 : ℝ) ^ y = (2 : ℝ) ^ (2 * y) := by
  have hfour : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [← hfour, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The squared radius gap, expressed as a power of four. -/
theorem deGiorgiRadius_sub_succ_sq (r R : ℝ) (n : ℕ) :
    (deGiorgiRadius r R n - deGiorgiRadius r R (n + 1)) ^ 2 =
      (R - r) ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)) := by
  rw [deGiorgiRadius_sub_succ, mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), four_rpow_eq]
  congr 1
  push_cast
  ring

/-- The squared level gap, expressed as a power of four. -/
theorem deGiorgiLevel_succ_sub_sq (K : ℝ) (n : ℕ) :
    (deGiorgiLevel K (n + 1) - deGiorgiLevel K n) ^ 2 =
      K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)) := by
  rw [deGiorgiLevel_succ_sub, mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), four_rpow_eq]
  congr 1
  push_cast
  ring

theorem deGiorgiRadius_pos {r R : ℝ} (hr : 0 < r) (hR : r < R) (n : ℕ) :
    0 < deGiorgiRadius r R n := by
  rw [deGiorgiRadius]
  have hpow : 0 < (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdiff : 0 < R - r := sub_pos.mpr hR
  nlinarith [mul_pos hdiff hpow]

theorem deGiorgiRadius_lower_lt {r R : ℝ} (hR : r < R) (n : ℕ) :
    r < deGiorgiRadius r R n := by
  rw [deGiorgiRadius]
  have hpow : 0 < (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith

theorem deGiorgiRadius_strictAnti {r R : ℝ} (hR : r < R) :
    StrictAnti (deGiorgiRadius r R) := by
  intro n m hnm
  rw [deGiorgiRadius, deGiorgiRadius]
  have hpow : (2 : ℝ) ^ (-(m : ℝ)) < (2 : ℝ) ^ (-(n : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    exact neg_lt_neg (by exact_mod_cast hnm)
  nlinarith

theorem deGiorgiRadius_antitone {r R : ℝ} (hR : r < R) :
    Antitone (deGiorgiRadius r R) :=
  (deGiorgiRadius_strictAnti hR).antitone

theorem deGiorgiRadius_le_upper {r R : ℝ} (hR : r < R) (n : ℕ) :
    deGiorgiRadius r R n ≤ R := by
  calc
    deGiorgiRadius r R n ≤ deGiorgiRadius r R 0 :=
      (deGiorgiRadius_antitone hR) (Nat.zero_le n)
    _ = R := deGiorgiRadius_zero r R

theorem deGiorgiLevel_nonneg {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ deGiorgiLevel K n := by
  rw [deGiorgiLevel]
  have hpow_pos : 0 < (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpow_le_one : (2 : ℝ) ^ (-(n : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num)]
    exact (inv_le_one₀ (Real.rpow_pos_of_pos (by norm_num) (n : ℝ))).mpr
      (Real.one_le_rpow (by norm_num) (by positivity))
  exact mul_nonneg hK (sub_nonneg.mpr hpow_le_one)

theorem deGiorgiLevel_lt {K : ℝ} (hK : 0 < K) (n : ℕ) :
    deGiorgiLevel K n < K := by
  rw [deGiorgiLevel]
  have hpow : 0 < (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  nlinarith

theorem deGiorgiLevel_strictMono {K : ℝ} (hK : 0 < K) :
    StrictMono (deGiorgiLevel K) := by
  intro n m hnm
  rw [deGiorgiLevel, deGiorgiLevel]
  have hpow : (2 : ℝ) ^ (-(m : ℝ)) < (2 : ℝ) ^ (-(n : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    exact neg_lt_neg (by exact_mod_cast hnm)
  nlinarith

theorem deGiorgiLevel_monotone {K : ℝ} (hK : 0 < K) :
    Monotone (deGiorgiLevel K) :=
  (deGiorgiLevel_strictMono hK).monotone

/-- Later De Giorgi balls are contained in earlier ones. -/
theorem euclideanBall_deGiorgiRadius_subset_of_le
    {d : ℕ} {x₀ : Vec d} {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {n m : ℕ} (hnm : n ≤ m) :
    euclideanBall x₀ (deGiorgiRadius r R m) ⊆
      euclideanBall x₀ (deGiorgiRadius r R n) := by
  exact euclideanBall_mono
    (deGiorgiRadius_pos hr hR m).le
    ((deGiorgiRadius_antitone hR) hnm)

/-- Consecutive De Giorgi balls are nested. -/
theorem euclideanBall_deGiorgiRadius_succ_subset
    {d : ℕ} {x₀ : Vec d} {r R : ℝ} (hr : 0 < r) (hR : r < R) (n : ℕ) :
    euclideanBall x₀ (deGiorgiRadius r R (n + 1)) ⊆
      euclideanBall x₀ (deGiorgiRadius r R n) := by
  exact euclideanBall_deGiorgiRadius_subset_of_le hr hR (Nat.le_succ n)

/-- Every De Giorgi ball lies inside the initial ball. -/
theorem euclideanBall_deGiorgiRadius_subset
    {d : ℕ} {x₀ : Vec d} {r R : ℝ} (hr : 0 < r) (hR : r < R) (n : ℕ) :
    euclideanBall x₀ (deGiorgiRadius r R n) ⊆ euclideanBall x₀ R := by
  exact euclideanBall_mono
    (deGiorgiRadius_pos hr hR n).le
    (deGiorgiRadius_le_upper hR n)

private theorem tendsto_two_rpow_neg :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine hpow.congr' ?_
  filter_upwards [] with n
  rw [← Real.rpow_natCast]
  exact (Real.rpow_neg_eq_inv_rpow 2 (n : ℝ)).symm

theorem tendsto_deGiorgiRadius (r R : ℝ) :
    Tendsto (deGiorgiRadius r R) atTop (𝓝 r) := by
  simpa only [deGiorgiRadius, mul_zero, add_zero] using!
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_two_rpow_neg)

theorem tendsto_deGiorgiLevel (K : ℝ) :
    Tendsto (deGiorgiLevel K) atTop (𝓝 K) := by
  have hdiff : Tendsto (fun n : ℕ => 1 - (2 : ℝ) ^ (-(n : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_two_rpow_neg
  simpa only [mul_one] using! tendsto_const_nhds.mul hdiff

end PDE
