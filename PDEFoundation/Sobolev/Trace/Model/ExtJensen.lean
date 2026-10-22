module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A weighted Jensen inequality in `ℝ≥0∞`

`(∫⁻ w f)^p ≤ (∫⁻ w)^(p-1) ∫⁻ w f^p` for `p > 1`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

theorem lintegral_rpow_le_mul_measure_univ {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : ℝ} (hp : 1 < p) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ p ≤ μ univ ^ (p - 1) * ∫⁻ a, f a ^ p ∂μ := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hqdef
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq.symm (f := fun _ => (1 : ℝ≥0∞)) (g := f)
    aemeasurable_const hf
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const] at h
  have hsum : p⁻¹ + q⁻¹ = 1 := hpq.inv_add_inv_eq_one
  have hp0 : 0 < p := by linarith
  have h2 := ENNReal.rpow_le_rpow h hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / q * p = p - 1 := by
    have : q⁻¹ = 1 - p⁻¹ := by linarith
    rw [one_div, this]
    field_simp
  have e2 : 1 / p * p = 1 := by field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  simpa using h2

theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ}
    (hp : 1 < p) {w f : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hf : AEMeasurable f μ) :
    (∫⁻ a, w a * f a ∂μ) ^ p ≤ (∫⁻ a, w a ∂μ) ^ (p - 1) * ∫⁻ a, w a * f a ^ p ∂μ := by
  have hf' : AEMeasurable f (μ.withDensity w) := hf.mono_ac (withDensity_absolutelyContinuous μ w)
  have h := lintegral_rpow_le_mul_measure_univ (μ.withDensity w) hp hf'
  rw [lintegral_withDensity_eq_lintegral_mul₀ hw hf,
    lintegral_withDensity_eq_lintegral_mul₀ hw (hf.pow_const p),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa using h

end PDE.TraceLane
