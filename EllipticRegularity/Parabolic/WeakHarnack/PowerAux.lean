/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyCutoffs
public import EllipticRegularity.Parabolic.WeakHarnack.PowerAlgebra

/-! # Integrability of `Q.indicator v^r` from finiteness of its lintegral -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE

variable {d : ℕ} {U : Set (Vec d)} {I : Set ℝ}

theorem lintegral_indicator_vr {Q : Set (Vec d × ℝ)} (hQ : MeasurableSet Q) (hQU : Q ⊆ U ×ˢ I)
    (f : Vec d × ℝ → ℝ) :
    ∫⁻ z in U ×ˢ I, ENNReal.ofReal (Q.indicator f z) = ∫⁻ z in Q, ENNReal.ofReal (f z) := by
  have : (fun z => ENNReal.ofReal (Q.indicator f z)) =
      Q.indicator (fun z => ENNReal.ofReal (f z)) := by
    funext z; by_cases hz : z ∈ Q <;> simp [hz]
  rw [this, lintegral_indicator hQ, Measure.restrict_restrict hQ, inter_eq_left.2 hQU]

theorem integrable_indicator_vr (u : ParH1Function U I)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {ε : ℝ} (hε : 0 < ε) (r : ℝ)
    {Q : Set (Vec d × ℝ)} (hQ : MeasurableSet Q) (hQU : Q ⊆ U ×ˢ I)
    (hR : ∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ r) ≠ ⊤) :
    Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I)) ∧
      (∫ z in U ×ˢ I, Q.indicator (fun z => (u.toFun z + ε) ^ r) z) =
        (∫⁻ z in Q, ENNReal.ofReal ((u.toFun z + ε) ^ r)).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (U ×ˢ I)] Q.indicator fun z => (u.toFun z + ε) ^ r := by
    filter_upwards [hu0] with z hz
    have : 0 < u.toFun z + ε := by linarith
    have := Real.rpow_pos_of_pos this r
    by_cases hzq : z ∈ Q <;> simp [hzq, this.le]
  have hmeas : AEStronglyMeasurable (Q.indicator fun z => (u.toFun z + ε) ^ r)
      (volume.restrict (U ×ˢ I)) :=
    (((u.memL2.aestronglyMeasurable.aemeasurable.add_const ε).pow_const r).aestronglyMeasurable).indicator hQ
  have hl := lintegral_indicator_vr hQ hQU (fun z => (u.toFun z + ε) ^ r)
  have hint : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I)) := by
    refine ⟨hmeas, ?_⟩
    have : ∫⁻ z in U ×ˢ I, ‖Q.indicator (fun z => (u.toFun z + ε) ^ r) z‖ₑ =
        ∫⁻ z in U ×ˢ I, ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hnn] with z hz
      rw [Real.enorm_eq_ofReal hz]
    rw [HasFiniteIntegral, this, hl]
    exact lt_top_iff_ne_top.2 hR
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hl]

theorem lintegral_indicator_vr' {Q : Set (Vec d × ℝ)} (hQ : MeasurableSet Q)
    (f : Vec d × ℝ → ℝ) :
    ∫⁻ z in U ×ˢ I, ENNReal.ofReal (Q.indicator f z) =
      ∫⁻ z in Q ∩ (U ×ˢ I), ENNReal.ofReal (f z) := by
  have : (fun z => ENNReal.ofReal (Q.indicator f z)) =
      Q.indicator (fun z => ENNReal.ofReal (f z)) := by
    funext z; by_cases hz : z ∈ Q <;> simp [hz]
  rw [this, lintegral_indicator hQ, Measure.restrict_restrict hQ]

theorem integrable_indicator_vr' (u : ParH1Function U I)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {ε : ℝ} (hε : 0 < ε) (r : ℝ)
    {Q : Set (Vec d × ℝ)} (hQ : MeasurableSet Q)
    (hR : ∫⁻ z in Q ∩ (U ×ˢ I), ENNReal.ofReal ((u.toFun z + ε) ^ r) ≠ ⊤) :
    Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I)) ∧
      (∫ z in U ×ˢ I, Q.indicator (fun z => (u.toFun z + ε) ^ r) z) =
        (∫⁻ z in Q ∩ (U ×ˢ I), ENNReal.ofReal ((u.toFun z + ε) ^ r)).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict (U ×ˢ I)] Q.indicator fun z => (u.toFun z + ε) ^ r := by
    filter_upwards [hu0] with z hz
    have : 0 < u.toFun z + ε := by linarith
    have := Real.rpow_pos_of_pos this r
    by_cases hzq : z ∈ Q <;> simp [hzq, this.le]
  have hmeas : AEStronglyMeasurable (Q.indicator fun z => (u.toFun z + ε) ^ r)
      (volume.restrict (U ×ˢ I)) :=
    (((u.memL2.aestronglyMeasurable.aemeasurable.add_const ε).pow_const r).aestronglyMeasurable).indicator hQ
  have hl := lintegral_indicator_vr' (U := U) (I := I) hQ (fun z => (u.toFun z + ε) ^ r)
  have hint : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I)) := by
    refine ⟨hmeas, ?_⟩
    have : ∫⁻ z in U ×ˢ I, ‖Q.indicator (fun z => (u.toFun z + ε) ^ r) z‖ₑ =
        ∫⁻ z in U ×ˢ I, ENNReal.ofReal (Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hnn] with z hz
      rw [Real.enorm_eq_ofReal hz]
    rw [HasFiniteIntegral, this, hl]
    exact lt_top_iff_ne_top.2 hR
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hl]

end PDE.Parabolic.WeakHarnack
