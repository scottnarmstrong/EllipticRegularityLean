module

public import PDEFoundation.Analysis.ENNRealMomentCancellation
public import PDEFoundation.Measure.CappedLocalizedDistributionMoment
public import PDEFoundation.Measure.WeightedMomentHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Sharp norm bounds for finite caps of localized maximal functions -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- On a finite measure space, actual localized distribution control gives
the sharp `q/(q-1)` norm bound for every finite cap. Finiteness of the cap
moment follows from its boundedness; the original maximal norm is not assumed
finite. -/
theorem eLpNorm_cappedENNReal_le_of_localized_distribution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (b : α → ℝ) {q : ℝ} (hq : 1 < q) (hb : MemLp b (ENNReal.ofReal q) μ)
    (F : α → ℝ≥0∞) (hF : Measurable F)
    (hdist : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < F x} ≤
        ∫⁻ x in {x | ENNReal.ofReal t < F x}, ENNReal.ofReal |b x| ∂μ)
    (N : NNReal) :
    eLpNorm (fun x => cappedENNReal (F x) N) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (q / (q - 1)) * eLpNorm b (ENNReal.ofReal q) μ := by
  let f : α → ℝ := fun x => cappedENNReal (F x) N
  have hf : Measurable f := PDE.Measurable.cappedENNReal hF N
  have hfnn (x : α) : 0 ≤ f x := cappedENNReal_nonneg _ _
  have hfMem : MemLp f (ENNReal.ofReal q) μ :=
    MemLp.of_bound hf.aestronglyMeasurable (N : ℝ) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]
      exact cappedENNReal_le (F x) N)
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq0
  have hpTop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMfinite := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop hfMem.eLpNorm_lt_top
  simp_rw [ENNReal.toReal_ofReal hq0.le, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (hfnn _), ENNReal.ofReal_rpow_of_nonneg (hfnn _) hq0.le] at hMfinite
  have hint := capped_moment_le_weighted_moment_of_localized_distribution
    μ b hb.aestronglyMeasurable F hF hq hdist N
  have hholder := weighted_moment_le_mul_q_moments μ b hb.aestronglyMeasurable
    f hf.aemeasurable hfnn hq
  have hcombine :
      ENNReal.ofReal (q - 1) * (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) ≤
        ENNReal.ofReal q *
          (∫⁻ x, ENNReal.ofReal (|b x| ^ q) ∂μ) ^ (1 / q) *
          (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) ^ ((q - 1) / q) := by
    exact hint.trans (by simpa only [mul_assoc] using mul_le_mul_right hholder (ENNReal.ofReal q))
  have hroot := rpow_le_of_moment_mul_le hq hMfinite.ne hcombine
  change eLpNorm f (ENNReal.ofReal q) μ ≤
    ENNReal.ofReal (q / (q - 1)) * eLpNorm b (ENNReal.ofReal q) μ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hb.aestronglyMeasurable]
  simp_rw [ENNReal.toReal_ofReal hq0.le, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg (hfnn _), ENNReal.ofReal_rpow_of_nonneg (hfnn _) hq0.le,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
  exact hroot

end PDE
