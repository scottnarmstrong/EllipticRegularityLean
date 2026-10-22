module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Basic

/-!
# Doubling the range of a local Hölder estimate on a convex set

A Hölder bound for pairs at Euclidean distance `< s` on a convex set gives one for pairs at distance
`< 2 s`, at the price of doubling the constant.  Also, the elementary bound
`1 / (1 - 2 ^ (-α)) ≤ 2 / α`.
-/

@[expose] public section

namespace PDE.CampanatoProof

variable {d : ℕ}

theorem holder_double {U : Set (Vec d)} (hU : Convex ℝ U) {f : Vec d → ℝ} {α H s : ℝ}
    (hα : 0 < α) (hH : 0 ≤ H)
    (h : ∀ y ∈ U, ∀ z ∈ U, vecEuclideanNorm (y - z) < s →
      |f y - f z| ≤ H * vecEuclideanNorm (y - z) ^ α) :
    ∀ y ∈ U, ∀ z ∈ U, vecEuclideanNorm (y - z) < 2 * s →
      |f y - f z| ≤ 2 * H * vecEuclideanNorm (y - z) ^ α := by
  intro y hy z hz hyz
  have hm : ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z) ∈ U :=
    hU hy hz (by norm_num) (by norm_num) (by norm_num)
  set m : Vec d := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z with hmdef
  set δ := vecEuclideanNorm (y - z) with hδ
  have h1 : y - m = (1 / 2 : ℝ) • (y - z) := by
    ext i; simp [hmdef]; ring
  have h2 : m - z = (1 / 2 : ℝ) • (y - z) := by
    ext i; simp [hmdef]; ring
  have hn : vecEuclideanNorm ((1 / 2 : ℝ) • (y - z)) = δ / 2 := by
    rw [vecEuclideanNorm_smul]; rw [abs_of_pos (by norm_num)]; ring
  have hδ0 : 0 ≤ δ := vecEuclideanNorm_nonneg _
  have hlt : δ / 2 < s := by linarith
  have hb1 := h y hy m hm (by rw [h1, hn]; exact hlt)
  have hb2 := h m hm z hz (by rw [h2, hn]; exact hlt)
  rw [h1, hn] at hb1
  rw [h2, hn] at hb2
  have hr : (δ / 2) ^ α ≤ δ ^ α := Real.rpow_le_rpow (by positivity) (by linarith) hα.le
  calc |f y - f z| = |(f y - f m) + (f m - f z)| := by ring_nf
    _ ≤ |f y - f m| + |f m - f z| := abs_add_le _ _
    _ ≤ H * (δ / 2) ^ α + H * (δ / 2) ^ α := add_le_add hb1 hb2
    _ ≤ 2 * H * δ ^ α := by nlinarith [mul_le_mul_of_nonneg_left hr hH]

/-- Bernoulli-type bound: `1 / (1 - 2 ^ (-α)) ≤ 2 / α` for `α ∈ (0, 1]`. -/
theorem inv_one_sub_two_rpow_neg_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    1 / (1 - (2 : ℝ) ^ (-α)) ≤ 2 / α := by
  have h := rpow_one_add_le_one_add_mul_self (s := -1 / 2) (by norm_num) hα.le hα1
  have h2 : (2 : ℝ) ^ (-α) = (1 / 2) ^ α := by
    rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    simp
  have h3 : (1 + -1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [h3] at h
  rw [h2]
  have hpos : 0 < 1 - (1 / 2 : ℝ) ^ α := by
    have : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
    linarith
  rw [div_le_div_iff₀ hpos hα]
  nlinarith

end PDE.CampanatoProof
