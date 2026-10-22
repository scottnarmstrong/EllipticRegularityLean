module

public import PDEFoundation.Measure.ENNRealMomentExhaustion
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

/-- Uniform bounds for a countable directed family bound its actual pointwise
supremum, without any prior finiteness assumption on the target. -/
theorem eLpNorm_iSup_le_of_directed
    {α β : Type*} [MeasurableSpace α] [Countable β] (μ : Measure α)
    (f : β → α → ℝ≥0∞) (hf : ∀ b, Measurable (f b))
    (hdir : Directed (· ≤ ·) f) {p : ℝ} (hp : 0 < p) {K : ℝ≥0∞}
    (hK : ∀ b, eLpNorm (f b) (ENNReal.ofReal p) μ ≤ K) :
    eLpNorm (fun x => ⨆ b, f b x) (ENNReal.ofReal p) μ ≤ K := by
  have hpne : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp
  have hformula (F : α → ℝ≥0∞) (hF : Measurable F) :
      eLpNorm F (ENNReal.ofReal p) μ = (∫⁻ x, (F x) ^ p ∂μ) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top
        hF.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp.le]
    simp only [enorm_eq_self]
  have hmom (b : β) : (∫⁻ x, (f b x) ^ p ∂μ) ≤ K ^ p := by
    have h := ENNReal.rpow_le_rpow (hK b) hp.le
    rw [hformula _ (hf b), ← ENNReal.rpow_mul,
      show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one] at h
    exact h
  have hdirPow : Directed (· ≤ ·) (fun b x => (f b x) ^ p) := by
    intro b c
    obtain ⟨a, hba, hca⟩ := hdir b c
    exact ⟨a, fun x => ENNReal.rpow_le_rpow (hba x) hp.le,
      fun x => ENNReal.rpow_le_rpow (hca x) hp.le⟩
  have hsup (x : α) : (⨆ b, f b x) ^ p = ⨆ b, (f b x) ^ p := by
    exact (ENNReal.orderIsoRpow p hp).map_iSup _
  have hmoment : (∫⁻ x, (⨆ b, f b x) ^ p ∂μ) ≤ K ^ p := by
    simp_rw [hsup]
    rw [lintegral_iSup_directed_of_measurable (fun b => (hf b).pow_const p) hdirPow]
    exact iSup_le hmom
  rw [hformula _ (Measurable.iSup hf)]
  have h := ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp.le)
  rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one] at h
  exact h

end PDE
