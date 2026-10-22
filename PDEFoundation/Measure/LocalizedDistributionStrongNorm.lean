module

public import PDEFoundation.Measure.LocalizedDistributionCappedNorm
public import PDEFoundation.Measure.ENNRealMomentExhaustion

/-! # Sharp strong norms from actual localized distribution control -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- A localized distribution inequality on a finite measure space implies
the sharp strong norm bound. The conclusion follows by finite caps and
monotone convergence, without assuming the target norm finite. -/
theorem eLpNorm_le_of_localized_distribution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (b : α → ℝ) {q : ℝ} (hq : 1 < q) (hb : MemLp b (ENNReal.ofReal q) μ)
    (F : α → ℝ≥0∞) (hF : Measurable F)
    (hdist : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < F x} ≤
        ∫⁻ x in {x | ENNReal.ofReal t < F x}, ENNReal.ofReal |b x| ∂μ) :
    eLpNorm F (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (q / (q - 1)) * eLpNorm b (ENNReal.ofReal q) μ := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  have hpTop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  let K : ℝ≥0∞ := ENNReal.ofReal (q / (q - 1)) * eLpNorm b (ENNReal.ofReal q) μ
  have hcaps (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal
        ((cappedENNReal (F x) ((n + 1 : ℕ) : NNReal)) ^ q) ∂μ) ≤ K ^ q := by
    let N : NNReal := ((n + 1 : ℕ) : NNReal)
    let f : α → ℝ := fun x => cappedENNReal (F x) N
    have hfnn (x : α) : 0 ≤ f x := cappedENNReal_nonneg _ _
    have hcap := eLpNorm_cappedENNReal_le_of_localized_distribution μ b hq hb F hF hdist N
    have hpow := ENNReal.rpow_le_rpow hcap hq0.le
    have hmoment :
        eLpNorm f (ENNReal.ofReal q) μ ^ q =
          ∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop (f := f)
        (PDE.Measurable.cappedENNReal hF N).aestronglyMeasurable]
      simp_rw [ENNReal.toReal_ofReal hq0.le, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (hfnn _), ENNReal.ofReal_rpow_of_nonneg (hfnn _) hq0.le]
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
    change eLpNorm f (ENNReal.ofReal q) μ ^ q ≤ K ^ q at hpow
    rw [hmoment] at hpow
    exact hpow
  have hfull := lintegral_rpow_le_of_cappedENNReal μ F hF hq0 hcaps
  have hroot := ENNReal.rpow_le_rpow hfull (one_div_nonneg.mpr hq0.le)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] at hroot
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le]
  simpa only [enorm_eq_self] using hroot

end PDE
