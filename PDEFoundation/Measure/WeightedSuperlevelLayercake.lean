module

public import PDEFoundation.Measure.WeightedTailLayercake

/-! # Weighted layer cake for general nonnegative functions -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- Layer cake under the density `|b|` gives the literal weighted superlevel
identity. It permits arbitrary measures and infinite integrals. -/
theorem weighted_superlevel_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ)
    (f : α → ℝ) (hf : AEMeasurable f μ) (hfnn : ∀ x, 0 ≤ f x)
    {q : ℝ} (hq : 1 < q) :
    ENNReal.ofReal (q - 1) *
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x in {x | t < f x}, ENNReal.ofReal |b x| ∂μ) *
          ENNReal.ofReal (t ^ (q - 2))) =
      ∫⁻ x, ENNReal.ofReal |b x| * ENNReal.ofReal ((f x) ^ (q - 1)) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal |b x|)
  have hdensity : AEMeasurable (fun x => ENNReal.ofReal |b x|) μ := by
    simpa only [Real.enorm_eq_ofReal_abs] using hb.enorm
  have hfν : AEMeasurable f ν :=
    hf.mono_ac (withDensity_absolutelyContinuous μ _)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (ae_of_all _ hfnn) hfν (sub_pos.mpr hq)
  have htail (t : ℝ) : ν {x | t < f x} =
      ∫⁻ x in {x | t < f x}, ENNReal.ofReal |b x| ∂μ :=
    withDensity_apply₀ _ (hf.nullMeasurableSet_preimage measurableSet_Ioi)
  simp_rw [htail, show q - 1 - 1 = q - 2 by ring] at hlayer
  rw [← hlayer]
  exact lintegral_withDensity_eq_lintegral_mul₀ hdensity (hf.pow_const _).ennreal_ofReal

end PDE
