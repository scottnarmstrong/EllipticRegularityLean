/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PowerConv

/-! # `eLpNorm` of `u + ε` and `1/(u + ε)` against the normalized measure -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}

theorem cylMeasure_restrict_ac {α : Type*} [MeasureSpace α] (S T : Set α) :
    (cylMeasure S).restrict T ≪ volume.restrict T := by
  have h : cylMeasure S ≪ (volume : Measure α) :=
    (Measure.smul_absolutelyContinuous).trans (Measure.restrict_le_self.absolutelyContinuous)
  exact h.restrict T

/-- `u` is a.e.-strongly measurable for the normalized measure restricted to `T ⊆ U × I`. -/
theorem aesm_shift (u : ParH1Function U I) (S : Set (Vec d × ℝ)) {T : Set (Vec d × ℝ)}
    (hT : T ⊆ U ×ˢ I) (ε : ℝ) :
    AEStronglyMeasurable (fun z => u.toFun z + ε) ((cylMeasure S).restrict T) := by
  have h1 : AEStronglyMeasurable u.toFun (volume.restrict T) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hT le_rfl)
  exact ((h1.aemeasurable.add_const ε).aestronglyMeasurable).mono_ac (cylMeasure_restrict_ac S T)

theorem aesm_inv_shift (u : ParH1Function U I) (S : Set (Vec d × ℝ)) {T : Set (Vec d × ℝ)}
    (hT : T ⊆ U ×ˢ I) (ε : ℝ) :
    AEStronglyMeasurable (fun z => 1 / (u.toFun z + ε)) ((cylMeasure S).restrict T) := by
  have h1 : AEStronglyMeasurable u.toFun (volume.restrict T) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hT le_rfl)
  have : AEMeasurable (fun z => 1 / (u.toFun z + ε)) (volume.restrict T) := by
    exact ((h1.aemeasurable.add_const ε).inv).congr
      (Filter.Eventually.of_forall fun z => by simp [one_div])
  exact this.aestronglyMeasurable.mono_ac (cylMeasure_restrict_ac S T)

theorem lintegral_enorm_shift (u : ParH1Function U I)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {ε : ℝ} (hε : 0 < ε)
    {T : Set (Vec d × ℝ)} (hT : T ⊆ U ×ˢ I) {e : ℝ} (he : 0 ≤ e) :
    ∫⁻ z in T, ‖u.toFun z + ε‖ₑ ^ e = ∫⁻ z in T, ENNReal.ofReal ((u.toFun z + ε) ^ e) := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hu0] with z hz
  have : 0 ≤ u.toFun z + ε := by linarith
  rw [Real.enorm_of_nonneg this, ENNReal.ofReal_rpow_of_nonneg this he]

theorem lintegral_enorm_inv_shift (u : ParH1Function U I)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {ε : ℝ} (hε : 0 < ε)
    {T : Set (Vec d × ℝ)} (hT : T ⊆ U ×ˢ I) {e : ℝ} (he : 0 ≤ e) :
    ∫⁻ z in T, ‖1 / (u.toFun z + ε)‖ₑ ^ e =
      ∫⁻ z in T, ENNReal.ofReal ((u.toFun z + ε) ^ (-e)) := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hT hu0] with z hz
  have hpos : 0 < u.toFun z + ε := by linarith
  have h0 : 0 ≤ 1 / (u.toFun z + ε) := by positivity
  rw [Real.enorm_of_nonneg h0, ENNReal.ofReal_rpow_of_nonneg h0 he, one_div,
    Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]

end PDE.Parabolic.WeakHarnack
