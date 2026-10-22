module

public import PDEFoundation.Analysis.Inequalities.Bombieri.BallMeasure
public import PDEFoundation.Analysis.Inequalities.Bombieri.BallReal

/-!
# Step 2 of the Bombieri lemma: the hypothesis of the abstract lemma on `ν`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {d : ℕ}

/-- Transfer of the Bombieri hypothesis from the normalized ball norms to the norms for `ν`. -/
theorem ball_rh (q k A : ℝ) (hq : 0 < q) (hk : 0 < k) (hA : 0 < A) (v : Vec d → ℝ)
    (hyp : ∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ min 1 (q / 2) →
      eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
        ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / p)) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) s) (ENNReal.ofReal p) v)
    (r s : ℝ) (hr : 1 / 2 ≤ r) (hrs : r < s) (hs : s ≤ 1) (α : ℝ) (hα : 0 < α)
    (hαq : α ≤ min 1 (q / 2)) :
    eLpNorm v (ENNReal.ofReal q)
        ((normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict (euclideanBall 0 r)) ≤
      ENNReal.ofReal ((max 1 (volume (euclideanBall (0 : Vec d) 1)).toReal⁻¹ *
          max 1 ((2 ^ d * A) ^ 2) * (s - r) ^ (-(2 * k))) ^ (1 / α - 1 / q)) *
        eLpNorm v (ENNReal.ofReal α)
          ((normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict (euclideanBall 0 s)) := by
  have hr0 : 0 ≤ r := by linarith
  have hs0 : 0 < s := by linarith
  have h0 := hyp r s hr hrs hs α hα hαq
  rw [eLpMeanNormOn_ball_eq hs0 hs] at h0
  rw [eLpNorm_normalizedVolume_ball hr0 (by linarith), eLpNorm_normalizedVolume_ball hs0.le hs]
  rw [eLpNorm_normalizedVolume_ball hs0.le hs] at h0
  simp only [toReal_one_div_ofReal hq, toReal_one_div_ofReal hα] at h0 ⊢
  set ωE := volume (euclideanBall (0 : Vec d) 1) with hωE
  have hωtop : ωE ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  have hω : 0 < ωE.toReal := volume_euclideanBall_toReal_pos _ one_pos
  have hωeq : ωE⁻¹ = ENNReal.ofReal ωE.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hω, ENNReal.ofReal_toReal hωtop]
  set X := eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) r))
  set Y := eLpNorm v (ENNReal.ofReal α) (volumeOn (euclideanBall (0 : Vec d) s))
  have hd0 : 0 < s - r := by linarith
  have hreal := ball_constant_bound d ωE.toReal A q k α r s hω hA hq hk hα
    (by have := hαq; exact this.trans (min_le_right _ _)) hr hrs hs
  have hbracket : ωE⁻¹ ^ (1 / q) * ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / α)) *
      (ENNReal.ofReal (s ^ d))⁻¹ ^ (1 / α) ≤
      ENNReal.ofReal ((max 1 ωE.toReal⁻¹ * max 1 ((2 ^ d * A) ^ 2) * (s - r) ^ (-(2 * k))) ^
        (1 / α - 1 / q)) := by
    have hsd : 0 < s ^ d := pow_pos hs0 d
    have hq0 : 0 ≤ 1 / q := by positivity
    have hα0 : 0 ≤ 1 / α := by positivity
    rw [hωeq, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hω.le) hq0,
      ← ENNReal.ofReal_inv_of_pos hsd,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hsd.le) hα0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans (le_of_eq ?_) hreal
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 2
    field_simp
  calc ωE⁻¹ ^ (1 / q) * X
      ≤ ωE⁻¹ ^ (1 / q) * (ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / α)) *
          ((ENNReal.ofReal (s ^ d))⁻¹ ^ (1 / α) * (ωE⁻¹ ^ (1 / α) * Y))) := by gcongr
    _ = (ωE⁻¹ ^ (1 / q) * ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / α)) *
          (ENNReal.ofReal (s ^ d))⁻¹ ^ (1 / α)) * (ωE⁻¹ ^ (1 / α) * Y) := by ring
    _ ≤ _ := by gcongr

end PDE.Bombieri
