/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.Exhaustion

/-! # Whole-space energy identity by spatial exhaustion -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set Filter Topology

/-- The real-valued whole-space energy identity before conversion to `ENNReal`. -/
theorem cauchy_energy_identity_real_of_lt {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (hst : s < t)
    (ht : t ∈ Icc s T) :
    (∫ x : Vec d, u.toFun (x, t) ^ 2) +
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyEnergyDensity a u z = ∫ x : Vec d, f x ^ 2 := by
  let Et : ℕ → ℝ := fun n => ∫ x : Vec d,
    (cauchyExhaustionCutoff s T n).toFun (x, t) ^ 2 * u.toFun (x, t) ^ 2
  let Es : ℕ → ℝ := fun n => ∫ x : Vec d,
    (cauchyExhaustionCutoff s T n).toFun (x, s) ^ 2 * u.toFun (x, s) ^ 2
  let B : ℕ → ℝ := fun n => ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
    (cauchyExhaustionCutoff s T n).toFun z ^ 2 * cauchyEnergyDensity a u z
  let C : ℕ → ℝ := fun n => ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
    cauchyCutoffCrossFlux a u ((n : ℝ) + 2) (by positivity) z
  have hEt' := cauchy_cutoff_slice_integral_tendsto hsT ha f hf u hu ht
  have hEt : Tendsto Et atTop (𝓝 <| ∫ x : Vec d, u.toFun (x, t) ^ 2) := by
    simpa only [Et] using hEt'
  have hEs' := cauchy_cutoff_slice_integral_tendsto hsT ha f hf u hu ⟨le_rfl, hsT.le⟩
  have hEs : Tendsto Es atTop (𝓝 <| ∫ x : Vec d, u.toFun (x, s) ^ 2) := by
    simpa only [Es] using hEs'
  have hB' := cauchy_cutoff_bulk_integral_tendsto ha u ht
  have hB : Tendsto B atTop
      (𝓝 <| ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyEnergyDensity a u z) := by
    simpa only [B] using hB'
  let M := ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyFluxMajorant a u z
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun z => mul_nonneg (abs_nonneg _) <|
      Finset.sum_nonneg fun i _ => abs_nonneg _
  have hMfinite : IntegrableOn (cauchyFluxMajorant a u)
      ((univ : Set (Vec d)) ×ˢ Ioc s t) := cauchyFluxMajorant_integrable_Ioc ha u ht
  have hcoef : Tendsto (fun n : ℕ => (64 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hc := (tendsto_const_div_atTop_nhds_zero_nat (64 : ℝ)).comp
      (tendsto_add_atTop_nat 2)
    have heq : (fun n : ℕ => (64 : ℝ) / ((n : ℝ) + 2)) =
        (fun n : ℕ => (64 : ℝ) / (n : ℝ)) ∘ (fun n => n + 2) := by
      funext n
      simp [Function.comp_apply, Nat.cast_add]
    rw [heq]
    exact hc
  have htail : Tendsto (fun n : ℕ =>
      ((64 : ℝ) / ((n : ℝ) + 2)) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using hcoef.mul_const M
  have hCbound : ∀ n, ‖C n‖ ≤ ((64 : ℝ) / ((n : ℝ) + 2)) * M := by
    intro n
    have h := cauchy_cutoff_cross_integral_bound hsT ha u hu.1
      ((n : ℝ) + 2) (by positivity) ht hst
    simpa only [Real.norm_eq_abs, C, M] using h
  have hC : Tendsto C atTop (𝓝 0) := squeeze_zero_norm hCbound htail
  have hEsf : (∫ x : Vec d, u.toFun (x, s) ^ 2) = ∫ x : Vec d, f x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hu.2] with x hx
    rw [hx]
  have hEqn : ∀ n, Et n + 2 * B n + 2 * C n = Es n := by
    intro n
    have hR : 0 < (n : ℝ) + 2 := by positivity
    have hid := cauchy_cutoff_energy_identity hsT ha u hu.1 ((n : ℝ) + 2) hR ht hst
    have hsplit := cauchy_cutoff_flux_integral_split hsT ha u hu.1 ((n : ℝ) + 2) hR ht hst
    rw [hsplit] at hid
    simp only [setIntegral_univ] at hid
    dsimp [Et, Es, B, C, cauchyExhaustionCutoff]
    nlinarith [hid]
  have hsum : Tendsto (fun n => Et n + 2 * B n + 2 * C n) atTop
      (𝓝 ((∫ x : Vec d, u.toFun (x, t) ^ 2) +
        2 * (∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyEnergyDensity a u z))) := by
    have h := (hEt.add (hB.const_mul 2)).add (hC.const_mul 2)
    simpa only [mul_zero, add_zero] using h
  have hEsLimit : Tendsto Es atTop (𝓝 <| ∫ x : Vec d, u.toFun (x, s) ^ 2) := hEs
  have hEqEvent : (fun n => Et n + 2 * B n + 2 * C n) =ᶠ[atTop] Es :=
    Filter.Eventually.of_forall hEqn
  have hsumEs : Tendsto (fun n => Et n + 2 * B n + 2 * C n) atTop
      (𝓝 <| ∫ x : Vec d, u.toFun (x, s) ^ 2) :=
    Tendsto.congr' hEqEvent.symm hEsLimit
  have hlim := tendsto_nhds_unique hsum hsumEs
  calc
    (∫ x : Vec d, u.toFun (x, t) ^ 2) +
        2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t, cauchyEnergyDensity a u z =
      (∫ x : Vec d, u.toFun (x, s) ^ 2) := hlim
    _ = ∫ x : Vec d, f x ^ 2 := hEsf

/-- The whole-space energy identity, including the initial time slice. -/
theorem cauchy_energy_identity_real {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    (∫ x : Vec d, u.toFun (x, t) ^ 2) +
      2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyEnergyDensity a u z = ∫ x : Vec d, f x ^ 2 := by
  by_cases hst : s < t
  · exact cauchy_energy_identity_real_of_lt hsT ha f hf u hu hst ht
  · have hts : t = s := le_antisymm (le_of_not_gt hst) ht.1
    subst t
    have hinit : (∫ x : Vec d, u.toFun (x, s) ^ 2) = ∫ x : Vec d, f x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hu.2] with x hx
      rw [hx]
    simp [hinit]

end PDE.Parabolic.Cauchy.Energy
