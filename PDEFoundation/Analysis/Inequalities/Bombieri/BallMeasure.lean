module

public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Analysis.Inequalities.Bombieri.OneStep

/-!
# Measure-theoretic bookkeeping for the Bombieri lemma on the unit ball

`ν = normalizedVolumeOn (B 1)` is the probability measure of the manuscript proof; its restriction to
`B σ` is the inverse unit-ball volume times the volume restricted to `B σ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {d : ℕ}

theorem toReal_one_div_ofReal {α : ℝ} (hα : 0 < α) :
    (1 / ENNReal.ofReal α).toReal = 1 / α := by
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hα.le]; simp

/-- Restriction of the normalized unit-ball measure to a smaller ball. -/
theorem normalizedVolume_restrict_ball {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict (euclideanBall 0 σ) =
      (volume (euclideanBall (0 : Vec d) 1))⁻¹ • volumeOn (euclideanBall (0 : Vec d) σ) := by
  rw [normalizedVolumeOn, Measure.restrict_smul]
  congr 1
  rw [volumeOn, volumeOn, Measure.restrict_restrict (isOpen_euclideanBall _ _).measurableSet,
    Set.inter_eq_left.mpr (euclideanBall_mono hσ0 hσ1)]

theorem eLpNorm_normalizedVolume_ball {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (g : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm g p ((normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict
        (euclideanBall 0 σ)) =
      (volume (euclideanBall (0 : Vec d) 1))⁻¹ ^ (1 / p).toReal *
        eLpNorm g p (volumeOn (euclideanBall (0 : Vec d) σ)) := by
  rw [normalizedVolume_restrict_ball hσ0 hσ1,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr
      (volume_euclideanBall_ne_top _ zero_le_one))]
  rfl

/-- The normalized `L^p` norm on `B s` is `s^{-d/p}` times the norm for `ν`. -/
theorem eLpMeanNormOn_ball_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (g : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpMeanNormOn (euclideanBall (0 : Vec d) s) p g =
      (ENNReal.ofReal (s ^ d))⁻¹ ^ (1 / p).toReal *
        eLpNorm g p ((normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict
          (euclideanBall 0 s)) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hs0.le)),
    eLpNorm_normalizedVolume_ball hs0.le hs1, volume_euclideanBall_eq_unit_mul_of_pos _ hs0,
    ENNReal.mul_inv (Or.inr (volume_euclideanBall_ne_top _ zero_le_one))
      (Or.inr (volume_euclideanBall_pos _ one_pos).ne'),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), mul_assoc]
  rfl

end PDE.Bombieri
