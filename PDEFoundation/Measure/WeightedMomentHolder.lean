module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import PDEFoundation.Measure.WeightedSuperlevelLayercake

/-! # Hölder for the weighted moment in a maximal estimate -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- Actual Hölder with conjugate exponents bounds a weighted `q-1` moment
by the two literal `q` moments. Infinite moments are allowed. -/
theorem weighted_moment_le_mul_q_moments
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ)
    (f : α → ℝ) (hf : AEMeasurable f μ) (hfnn : ∀ x, 0 ≤ f x)
    {q : ℝ} (hq : 1 < q) :
    (∫⁻ x, ENNReal.ofReal |b x| * ENNReal.ofReal ((f x) ^ (q - 1)) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (|b x| ^ q) ∂μ) ^ (1 / q) *
        (∫⁻ x, ENNReal.ofReal ((f x) ^ q) ∂μ) ^ ((q - 1) / q) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hbENN : AEMeasurable (fun x => ENNReal.ofReal |b x|) μ := by
    simpa only [Real.enorm_eq_ofReal_abs] using hb.enorm
  have h := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
    (Real.HolderConjugate.conjExponent hq) hbENN hf.ennreal_ofReal
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (hfnn _) (sub_nonneg.mpr hq.le),
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le,
    ENNReal.ofReal_rpow_of_nonneg (hfnn _) hq0.le] at h
  have hexponent : 1 / Real.conjExponent q = (q - 1) / q := by
    simp only [Real.conjExponent, one_div_div]
  rwa [hexponent] at h

end PDE
