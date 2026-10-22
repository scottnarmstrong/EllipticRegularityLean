module

public import PDEFoundation.Analysis.Gehring.LocalIteration
public import PDEFoundation.Analysis.Gehring.IterationSum

/-!
# The radii of the localization iteration

`ρ_j = 3/4 - 2^{-j}/4`: `ρ_0 = 1/2`, `1/2 ≤ ρ_j < ρ_{j+1} ≤ 3/4`, gap `2^{-j}/8`, and
`T_{ρ_j, ρ_{j+1}} = (24 √d)^{d+1} 2^{j(d+1)} m`.
-/

@[expose] public section

namespace PDE.Gehring

/-- The radius `ρ_j = 3/4 - 2^{-j}/4`. -/
noncomputable def gehringRadius (j : ℕ) : ℝ := 3 / 4 - (1 / 2 : ℝ) ^ j / 4

theorem gehringRadius_zero : gehringRadius 0 = 1 / 2 := by
  unfold gehringRadius; norm_num

theorem half_le_gehringRadius (j : ℕ) : 1 / 2 ≤ gehringRadius j := by
  unfold gehringRadius
  have : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem gehringRadius_le (j : ℕ) : gehringRadius j ≤ 3 / 4 := by
  unfold gehringRadius
  have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  linarith

theorem gehringRadius_sub (j : ℕ) :
    gehringRadius (j + 1) - gehringRadius j = (1 / 2 : ℝ) ^ j / 8 := by
  unfold gehringRadius
  rw [pow_succ]
  ring

theorem gehringRadius_lt (j : ℕ) : gehringRadius j < gehringRadius (j + 1) := by
  have := gehringRadius_sub j
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ j / 8 := by positivity
  linarith

theorem gehringRadius_threshold (d j : ℕ) (m : ℝ) :
    (3 * Real.sqrt d / (gehringRadius (j + 1) - gehringRadius j)) ^ (d + 1) * m =
      (24 * Real.sqrt d) ^ (d + 1) * 2 ^ (j * (d + 1)) * m := by
  rw [gehringRadius_sub, pow_mul]
  congr 2
  rw [one_div, inv_pow]
  field_simp
  ring

end PDE.Gehring
