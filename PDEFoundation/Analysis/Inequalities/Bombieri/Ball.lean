module

public import PDEFoundation.Analysis.Inequalities.Bombieri.Abstract
public import PDEFoundation.Analysis.Inequalities.Bombieri.BallRh
public import PDEFoundation.Analysis.Inequalities.Bombieri.BallLog

/-!
# The Bombieri lemma on the unit ball (Lemma 1.13)

Application of the abstract Bombieri-Giusti lemma exactly as in the manuscript: `U σ = B σ`,
`δ = 1/2`, `ν` the normalized volume of `B 1`, `α₀ = q`, `m = 2k` and
`c = max 1 ω⁻¹ * max 1 ((2^d A)^2)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

/-- The Bombieri lemma for measurable, everywhere positive representatives. -/
theorem exists_bombieri_core (d : ℕ) (q k A : ℝ) (hq : 0 < q) (hk : 0 < k) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Vec d → ℝ, Measurable v → (∀ x, 0 < v x) →
      eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) < ⊤ →
      eLpNorm (fun x => Real.log (v x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal A →
      (∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ min 1 (q / 2) →
        eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / p)) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) s) (ENNReal.ofReal p) v) →
      eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        ENNReal.ofReal C := by
  set ωE := volume (euclideanBall (0 : Vec d) 1) with hωE
  have hωtop : ωE ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  have hω : 0 < ωE.toReal := volume_euclideanBall_toReal_pos _ one_pos
  have hωpos : 0 < ωE := volume_euclideanBall_pos _ one_pos
  set c : ℝ := max 1 ωE.toReal⁻¹ * max 1 ((2 ^ d * A) ^ 2) with hc
  have hc1 : 1 ≤ c := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hωA : ωE.toReal⁻¹ * A ≤ c := by
    have h1 : ωE.toReal⁻¹ ≤ max 1 ωE.toReal⁻¹ := le_max_right _ _
    have h2 : A ≤ max 1 ((2 ^ d * A) ^ 2) := by
      by_cases hA1 : A ≤ 1
      · exact hA1.trans (le_max_left _ _)
      · push Not at hA1
        have h2d : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
        have h3 : A ≤ 2 ^ d * A := le_mul_of_one_le_left hA.le h2d
        have h4 : 2 ^ d * A ≤ (2 ^ d * A) ^ 2 := by nlinarith
        exact (h3.trans h4).trans (le_max_right _ _)
    exact mul_le_mul h1 h2 hA.le (by positivity)
  set G := giustiConst (1 / 2) q c (2 * k) with hG
  refine ⟨ωE.toReal ^ (1 / q) * G, mul_pos (Real.rpow_pos_of_pos hω _) (giustiConst_pos _ _ _ _),
    ?_⟩
  intro v hv hpos hfin hlogv hyp
  have : IsProbabilityMeasure (normalizedVolumeOn (euclideanBall (0 : Vec d) 1)) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hωpos hωtop.lt_top
  have hmain := bombieri_giusti (1 / 2) q c (2 * k) (by norm_num) (by norm_num) hq hc1
    (by positivity) (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))
    (fun σ => euclideanBall (0 : Vec d) σ)
    (fun σ _ _ => (isOpen_euclideanBall _ _).measurableSet)
    (fun σ' σ h1 h2 _ => euclideanBall_mono (by linarith) h2)
    v hv hpos
    (by
      show eLpNorm v _ ((normalizedVolumeOn (euclideanBall (0 : Vec d) 1)).restrict
        (euclideanBall 0 1)) < ⊤
      rw [eLpNorm_normalizedVolume_ball zero_le_one le_rfl]
      exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.inv_ne_top.mpr hωpos.ne')) hfin)
    (fun lam hlam => (ball_log_tail A hA v hv hlogv lam hlam).trans (ENNReal.ofReal_le_ofReal (by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hωA hlam.le)))
    (fun σ' σ h1 h2 h3 α hα hαq => ball_rh q k A hq hk hA v hyp σ' σ h1 h2 h3 α hα hαq)
  beta_reduce at hmain
  rw [eLpNorm_normalizedVolume_ball (by norm_num) (by norm_num),
    toReal_one_div_ofReal hq] at hmain
  have hX : eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) =
      ωE ^ (1 / q) * (ωE⁻¹ ^ (1 / q) *
        eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2)))) := by
    rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_inv_cancel hωpos.ne' hωtop, ENNReal.one_rpow, one_mul]
  rw [hX]
  calc ωE ^ (1 / q) * (ωE⁻¹ ^ (1 / q) *
        eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))))
      ≤ ωE ^ (1 / q) * ENNReal.ofReal G := by gcongr
    _ = ENNReal.ofReal (ωE.toReal ^ (1 / q) * G) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hω.le _),
        ← ENNReal.ofReal_rpow_of_nonneg hω.le (by positivity), ENNReal.ofReal_toReal hωtop]


end PDE.Bombieri
