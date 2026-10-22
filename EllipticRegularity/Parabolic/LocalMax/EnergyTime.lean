/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.EnergyRamp
public import EllipticRegularity.Parabolic.LocalMax.EnergyLebesgueENN

/-! # The time-slice part of the power energy estimate

For almost every `t`, `∫_U η² F(u)(t) ≤ R`: Tonelli reduces the fixed-ramp inequality to a bound on
smooth one-sided time averages of the slice integral `G(t)`, and Lebesgue points finish.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain PDE.Parabolic.WeakSlice

variable {d : ℕ} {U : Set (Vec d)} {Lam : ℝ} {a : ParCoeffField d}
  {u : ParH1Function U (Ioc (-1 : ℝ) 0)} {F : ℝ → ℝ} {K : ℝ} {η : Vec d × ℝ → ℝ}
  {Kx : Set (Vec d)} {T tTop δ : ℝ}

theorem restrict_prod_eq_prod (U : Set (Vec d)) (s t : ℝ) :
    volume.restrict (U ×ˢ Ioo s t) = (volume.restrict U).prod (volume.restrict (Ioo s t)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

/-- Tonelli on `U ×ˢ Ioo s t`, integrating the space variable first. -/
theorem lintegral_prod_slices_Ioo {f : Vec d × ℝ → ℝ≥0∞} {s t : ℝ}
    (hf : AEMeasurable f (volume.restrict (U ×ˢ Ioo s t))) :
    ∫⁻ z in U ×ˢ Ioo s t, f z = ∫⁻ τ in Ioo s t, ∫⁻ x in U, f (x, τ) := by
  rw [restrict_prod_eq_prod] at hf ⊢
  exact lintegral_prod_symm f hf

/-- The time-slice estimate. -/
theorem energy_time_estimate (H : EnergyHyp U Lam a u F K η Kx T tTop δ) :
    ∀ᵐ t ∂(volume.restrict (Ioo T tTop)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, t) ^ 2 * F (u.toFun (x, t))) ≤
        energyBound Lam K F u η T tTop := by
  by_cases hR : energyBound Lam K F u η T tTop = ⊤
  · exact Eventually.of_forall fun _ => by rw [hR]; exact le_top
  have hη1 := H.contDiffη_one
  have hsub : U ×ˢ Ioo T tTop ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := prod_mono subset_rfl fun t ht =>
    ⟨by linarith [ht.1, H.hT], by linarith [ht.2, H.htTop]⟩
  have hum : AEStronglyMeasurable u.toFun (volume.restrict (U ×ˢ Ioo T tTop)) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  let Hf : Vec d × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (η z ^ 2 * F (u.toFun z))
  have hHm : AEMeasurable Hf (volume.restrict (U ×ˢ Ioo T tTop)) := by
    have h1 : AEStronglyMeasurable (fun z => F (u.toFun z)) (volume.restrict (U ×ˢ Ioo T tTop)) :=
      H.contDiffF.continuous.comp_aestronglyMeasurable hum
    have h2 : Continuous fun z : Vec d × ℝ => η z ^ 2 := hη1.continuous.pow 2
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (h2.aestronglyMeasurable.mul h1).aemeasurable
  have hHm' := hHm
  rw [restrict_prod_eq_prod] at hHm'
  have hGm : AEMeasurable (fun τ => ∫⁻ x in U, Hf (x, τ)) (volume.restrict (Ioo T tTop)) :=
    hHm'.lintegral_prod_left'
  refine ae_le_of_ramp_bounds hR hGm fun t₁ ht₁ h hh => ?_
  have hcore := (ramp_energy_core H (χ := timeRamp t₁ h)
    ((timeRamp_contDiff _ _).of_le (by exact_mod_cast le_top)) (timeRamp_nonneg _ _)
    (timeRamp_le_one _ _)
    (fun t => by
      rw [deriv_timeRamp]
      exact neg_nonpos.2 (rampKernel_nonneg hh t))
    ht₁.2 (fun t ht => timeRamp_eq_zero hh ht)).1
  refine le_trans (le_of_eq ?_) hcore
  have hpt : ∀ z : Vec d × ℝ, ENNReal.ofReal (F (u.toFun z) * η z ^ 2 *
      (-deriv (timeRamp t₁ h) z.2)) = ENNReal.ofReal (rampKernel t₁ h z.2) * Hf z := by
    intro z
    rw [deriv_timeRamp, neg_neg, ← ENNReal.ofReal_mul (rampKernel_nonneg hh _)]
    congr 1; ring
  simp_rw [hpt]
  rw [lintegral_prod_slices_Ioo]
  · refine lintegral_congr fun τ => ?_
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  · exact (ENNReal.measurable_ofReal.comp
      ((rampKernel_continuous t₁ h).measurable.comp measurable_snd)).aemeasurable.mul hHm

end PDE.Parabolic.LocalMax
