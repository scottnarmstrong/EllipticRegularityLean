module

public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The radius `ρ = (3/4)^{1/d}` of the expansion-of-positivity proof
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- The fixed radius `ρ = (3/4)^{1/d}` (manuscript: Proposition 4.11). -/
noncomputable def expRho (d : ℕ) : ℝ := (3 / 4 : ℝ) ^ ((1 : ℝ) / d)

theorem expRho_pow {d : ℕ} (hd : 1 ≤ d) : expRho d ^ d = 3 / 4 := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  unfold expRho
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [one_div_mul_cancel hd', Real.rpow_one]

theorem expRho_pos (d : ℕ) : 0 < expRho d := by unfold expRho; positivity

theorem expRho_lt_one {d : ℕ} (hd : 1 ≤ d) : expRho d < 1 := by
  unfold expRho
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

theorem three_quarters_le_expRho {d : ℕ} (hd : 1 ≤ d) : 3 / 4 ≤ expRho d := by
  unfold expRho
  have h1 : (1 : ℝ) / d ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hd
  calc (3 / 4 : ℝ) = (3 / 4 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h1

/-- `|B_ρ| = (3/4) |B_1|`. -/
theorem volume_expRho_ball {d : ℕ} (hd : 1 ≤ d) :
    volume (euclideanBall (0 : Vec d) (expRho d)) =
      ENNReal.ofReal (3 / 4) * volume (euclideanBall (0 : Vec d) 1) := by
  rw [volume_euclideanBall_eq_unit_mul_of_pos _ (expRho_pos d), expRho_pow hd]

end PDE.DGNMLog
