module

public import PDEFoundation.Analysis.Inequalities.Bombieri.BallMeasure

/-!
# Chebyshev step of the Bombieri lemma (Step 1)
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {d : ℕ}

theorem ball_log_tail (A : ℝ) (_hA : 0 < A) (v : Vec d → ℝ) (hv : Measurable v)
    (hlogv : eLpNorm (fun x => Real.log (v x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal A) (lam : ℝ) (hlam : 0 < lam) :
    normalizedVolumeOn (euclideanBall (0 : Vec d) 1)
        (euclideanBall 0 1 ∩ {x | lam < Real.log (v x)}) ≤
      ENNReal.ofReal ((volume (euclideanBall (0 : Vec d) 1)).toReal⁻¹ * (A / lam)) := by
  set μ := volumeOn (euclideanBall (0 : Vec d) 1) with hμ
  set ωE := volume (euclideanBall (0 : Vec d) 1) with hωE
  have hωtop : ωE ≠ ⊤ := volume_euclideanBall_ne_top _ zero_le_one
  have hω : 0 < ωE.toReal := volume_euclideanBall_toReal_pos _ one_pos
  have hωeq : ωE = ENNReal.ofReal ωE.toReal := (ENNReal.ofReal_toReal hωtop).symm
  have hmeas : AEMeasurable (fun x => ‖Real.log (v x)‖ₑ) μ :=
    (hv.log.enorm).aemeasurable
  have hmark := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal lam)
  rw [← eLpNorm_one_eq_lintegral_enorm hv.log.aestronglyMeasurable] at hmark
  have hmark' := hmark.trans hlogv
  set m := μ {x | ENNReal.ofReal lam ≤ ‖Real.log (v x)‖ₑ} with hm
  have hm2 : m ≤ ENNReal.ofReal A / ENNReal.ofReal lam := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hlam)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hmark'
  have hS : μ (euclideanBall 0 1 ∩ {x | lam < Real.log (v x)}) ≤ m := by
    refine measure_mono ?_
    intro x hx
    have hx2 : lam < Real.log (v x) := hx.2
    show ENNReal.ofReal lam ≤ ‖Real.log (v x)‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hx2.le.trans (le_abs_self _))
  calc normalizedVolumeOn (euclideanBall (0 : Vec d) 1)
        (euclideanBall 0 1 ∩ {x | lam < Real.log (v x)})
      = ωE⁻¹ * μ (euclideanBall 0 1 ∩ {x | lam < Real.log (v x)}) := by
        rw [normalizedVolumeOn, Measure.smul_apply, smul_eq_mul]
    _ ≤ ωE⁻¹ * (ENNReal.ofReal A / ENNReal.ofReal lam) := by gcongr; exact hS.trans hm2
    _ = ENNReal.ofReal ((volume (euclideanBall (0 : Vec d) 1)).toReal⁻¹ * (A / lam)) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hω.le), ENNReal.ofReal_inv_of_pos hω,
          ENNReal.ofReal_div_of_pos hlam, ← hωeq]

end PDE.Bombieri
