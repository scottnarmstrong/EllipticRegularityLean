module

public import PDEFoundation.Measure.WeightedMomentHolder

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

/-- Hölder in actual Lp norms, allowing extended nonnegative target values. -/
theorem lintegral_abs_mul_le_eLpNorm_mul_conjugate
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ)
    (F : α → ℝ≥0∞) (hF : AEMeasurable F μ) {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal |b x| * F x ∂μ) ≤
      eLpNorm b (ENNReal.ofReal p) μ *
        eLpNorm F (ENNReal.ofReal (Real.conjExponent p)) μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (by simpa only [Real.enorm_eq_ofReal_abs] using hb.enorm) hF
  have hpne : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hp0
  have hqne : ENNReal.ofReal (Real.conjExponent p) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hpq.symm.pos
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top hb,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top hF.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hp0.le,
    ENNReal.toReal_ofReal hpq.symm.nonneg, Real.enorm_eq_ofReal_abs,
    enorm_eq_self, Pi.mul_apply] using h

end PDE
