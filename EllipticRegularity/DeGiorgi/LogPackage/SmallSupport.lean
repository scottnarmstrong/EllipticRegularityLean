module

public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.Inequalities.SobolevPoincare
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Holder inequality for functions supported on a small set
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

theorem sobolevConjugate_two_ge {d : ℕ} (hd : 3 ≤ d) : 2 ≤ sobolevConjugate d 2 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold sobolevConjugate
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem one_half_sub_inv_sobolevConjugate {d : ℕ} (hd : 3 ≤ d) :
    1 / (2 : ℝ) - 1 / sobolevConjugate d 2 = 1 / (d : ℝ) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have := inv_sobolevConjugate (d := d) (p := 2) (by norm_num) (by linarith)
  rw [one_div, one_div, this]
  ring

/-- Holder: `‖f‖_{L²(V)} ≤ ‖f‖_{L^{2*}(V)} |{f ≠ 0}|^{1/d}`. -/
theorem eLpNorm_two_le_of_ae_zero_off {d : ℕ} (hd : 3 ≤ d) {V t : Set (Vec d)}
    (ht : MeasurableSet t) {f : Vec d → ℝ} (hf : AEStronglyMeasurable f (volumeOn V))
    (hzero : ∀ᵐ x ∂(volumeOn V), x ∉ t → f x = 0) :
    eLpNorm f 2 (volumeOn V) ≤
      eLpNorm f (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn V) *
        volume (t ∩ V) ^ ((1 : ℝ) / d) := by
  set ν := volumeOn V with hν
  have hq2 : (2 : ENNReal) ≤ ENNReal.ofReal (sobolevConjugate d 2) := by
    have := sobolevConjugate_two_ge hd
    calc (2 : ENNReal) = ENNReal.ofReal 2 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal this
  have h1 : eLpNorm f 2 ν = eLpNorm f 2 (ν.restrict t) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict ht]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hzero] with x hx
    by_cases hxt : x ∈ t
    · simp [hxt]
    · simp [hxt, hx hxt]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict t) hq2
    (hf.mono_measure Measure.restrict_le_self)
  have h3 : eLpNorm f (ENNReal.ofReal (sobolevConjugate d 2)) (ν.restrict t) ≤
      eLpNorm f (ENNReal.ofReal (sobolevConjugate d 2)) ν :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  have hexp : 1 / (2 : ENNReal).toReal - 1 / (ENNReal.ofReal (sobolevConjugate d 2)).toReal =
      (1 : ℝ) / d := by
    rw [ENNReal.toReal_ofReal (by linarith [sobolevConjugate_two_ge hd])]
    simpa using one_half_sub_inv_sobolevConjugate hd
  have hmeas : (ν.restrict t) Set.univ = volume (t ∩ V) := by
    rw [Measure.restrict_apply_univ, hν, volumeOn, Measure.restrict_apply ht]
  rw [h1]
  refine h2.trans ?_
  rw [hexp, hmeas]
  gcongr

end PDE.DGNMLog
