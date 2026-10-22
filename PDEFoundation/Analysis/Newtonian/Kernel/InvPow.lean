module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Differences of inverse powers

For `x, y ∈ [r/2, 3r/2]`, `|x^{-m} - y^{-m}| ≤ m 8^m |x - y| / r^{m+1}`.
-/

@[expose] public section

namespace PDE

namespace NewtonKernelAux

theorem inv_pow_sub_le (m : ℕ) {r x y : ℝ} (hr : 0 < r) (hx : r / 2 ≤ x) (hx' : x ≤ 3 * r / 2)
    (hy : r / 2 ≤ y) (hy' : y ≤ 3 * r / 2) :
    |(x ^ m)⁻¹ - (y ^ m)⁻¹| ≤ m * 8 ^ m * |x - y| / r ^ (m + 1) := by
  rcases m with _ | n
  · simp
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxy : (x ^ (n + 1))⁻¹ - (y ^ (n + 1))⁻¹ = (y ^ (n + 1) - x ^ (n + 1)) / (x ^ (n + 1) * y ^ (n + 1)) := by
    field_simp
  rw [hxy, abs_div, abs_of_pos (mul_pos (pow_pos hx0 _) (pow_pos hy0 _))]
  have hnum : |y ^ (n + 1) - x ^ (n + 1)| ≤ |x - y| * (n + 1) * (3 * r / 2) ^ n := by
    have h1 := abs_pow_sub_pow_le (a := y) (b := x) (n := n + 1)
    have h2 : max |y| |x| ≤ 3 * r / 2 := by
      rw [abs_of_pos hy0, abs_of_pos hx0]; exact max_le hy' hx'
    have h3 : max |y| |x| ^ (n + 1 - 1) ≤ (3 * r / 2) ^ n := by
      simpa using pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg y)) h2 n
    calc _ ≤ |y - x| * ((n + 1 : ℕ) : ℝ) * max |y| |x| ^ (n + 1 - 1) := h1
      _ ≤ |y - x| * ((n + 1 : ℕ) : ℝ) * (3 * r / 2) ^ n := by gcongr
      _ = _ := by rw [abs_sub_comm]; push_cast; ring
  have hden : (r / 2) ^ (n + 1) * (r / 2) ^ (n + 1) ≤ x ^ (n + 1) * y ^ (n + 1) := by
    gcongr
  have hpos : 0 < (r / 2) ^ (n + 1) * (r / 2) ^ (n + 1) := by positivity
  calc |y ^ (n + 1) - x ^ (n + 1)| / (x ^ (n + 1) * y ^ (n + 1))
      ≤ (|x - y| * (n + 1) * (3 * r / 2) ^ n) / ((r / 2) ^ (n + 1) * (r / 2) ^ (n + 1)) := by
        gcongr
    _ ≤ _ := by
        rw [div_le_div_iff₀ hpos (by positivity)]
        have key : (3 / 2 : ℝ) ^ n * 4 ^ (n + 1) ≤ 8 ^ (n + 1) := by
          have h6 : (3 / 2 : ℝ) ^ n * 4 ^ n = 6 ^ n := by rw [← mul_pow]; norm_num
          have h8 : (6 : ℝ) ^ n ≤ 8 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
          have h8p : (0 : ℝ) < 8 ^ n := by positivity
          calc (3 / 2 : ℝ) ^ n * 4 ^ (n + 1) = 4 * ((3 / 2 : ℝ) ^ n * 4 ^ n) := by rw [pow_succ]; ring
            _ ≤ 8 ^ (n + 1) := by rw [h6, pow_succ]; linarith
        have e1 : (3 * r / 2) ^ n = (3 / 2) ^ n * r ^ n := by rw [← mul_pow]; ring_nf
        have e2 : (r / 2) ^ (n + 1) * (r / 2) ^ (n + 1) = r ^ (n + 1) * r ^ (n + 1) / 4 ^ (n + 1) := by
          have h4 : (4 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) := by rw [← mul_pow]; norm_num
          rw [div_pow, h4]
          field_simp
        rw [e1, e2]
        have hr1 : 0 < r ^ n := by positivity
        have : r ^ (n + 1) * r ^ (n + 1) = r ^ n * r ^ (n + 1 + 1) := by ring
        rw [this]
        push_cast
        have hq : 0 ≤ |x - y| * ((n : ℝ) + 1) := by positivity
        have h4 : (0:ℝ) < 4 ^ (n + 1) := by positivity
        rw [← mul_div_assoc, le_div_iff₀ h4]
        have : |x - y| * (↑n + 1) * ((3 / 2) ^ n * r ^ n) * r ^ (n + 1 + 1) * 4 ^ (n + 1)
            = (|x - y| * (↑n + 1)) * ((3 / 2) ^ n * 4 ^ (n + 1)) * (r ^ n * r ^ (n + 1 + 1)) := by ring
        rw [this]
        have : (↑n + 1) * 8 ^ (n + 1) * |x - y| * (r ^ n * r ^ (n + 1 + 1))
            = (|x - y| * (↑n + 1)) * 8 ^ (n + 1) * (r ^ n * r ^ (n + 1 + 1)) := by ring
        rw [this]
        gcongr

end NewtonKernelAux

end PDE
