/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.LocalMax.EnergyTest
public import EllipticRegularity.Parabolic.LocalMax.EnergyPointwise

/-! # The integrated power energy inequality for a fixed time ramp

For a smooth nonincreasing time profile `χ` with `0 ≤ χ ≤ 1` vanishing for `t ≥ t₁ < tTop`, testing
the renormalized equation with `η² χ` and applying Young's inequality gives
`∫ F(u) η² (-χ') ≤ R` and `∫ ½ F''(u) η² χ |∇u|² ≤ R`, with `R = energyBound`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.LocalMax

open MeasureTheory Set Filter Topology PDE PDE.Parabolic.Chain

/-- Right side of the power energy estimate. -/
noncomputable def energyBound {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (Lam K : ℝ) (F : ℝ → ℝ)
    (u : ParH1Function U I) (η : Vec d × ℝ → ℝ) (T tTop : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U ×ˢ Ioo T tTop, ENNReal.ofReal (F (u.toFun z) *
    (2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z)))

/-- The hypotheses of the power energy estimate. -/
structure EnergyHyp {d : ℕ} (U : Set (Vec d)) (Lam : ℝ) (a : ParCoeffField d)
    (u : ParH1Function U (Ioc (-1 : ℝ) 0)) (F : ℝ → ℝ) (K : ℝ) (η : Vec d × ℝ → ℝ)
    (Kx : Set (Vec d)) (T tTop δ : ℝ) : Prop where
  isOpen : IsOpen U
  coeff : IsParabolicCoeff 1 Lam a U (Ioc (-1 : ℝ) 0)
  solution : IsParabolicWeakSolution a U (Ioc (-1 : ℝ) 0) u
  pos : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z
  contDiffF : ContDiff ℝ 2 F
  bdd : ∃ C : NNReal, ∀ s, |deriv (deriv F) s| ≤ C
  K_nonneg : 0 ≤ K
  Fs : ∀ s, 0 ≤ s → 0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧ deriv F s ^ 2 ≤ K * deriv (deriv F) s * F s
  contDiffη : ContDiff ℝ (⊤ : ℕ∞) η
  compact : IsCompact Kx
  subset : Kx ⊆ U
  vanish_x : ∀ x t, x ∉ Kx → η (x, t) = 0
  hT : -1 < T
  hTt : T < tTop
  htTop : tTop ≤ 0
  hδ : 0 < δ
  vanish_t : ∀ x t, t ≤ T + δ → η (x, t) = 0

variable {d : ℕ} {U : Set (Vec d)} {Lam : ℝ} {a : ParCoeffField d}
  {u : ParH1Function U (Ioc (-1 : ℝ) 0)} {F : ℝ → ℝ} {K : ℝ} {η : Vec d × ℝ → ℝ}
  {Kx : Set (Vec d)} {T tTop δ : ℝ}

theorem restrict_prod_Ioo_eq (U : Set (Vec d)) (s t : ℝ) :
    volume.restrict (U ×ˢ Ioo s t) = volume.restrict (U ×ˢ Ioc s t) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc]

theorem continuous_parTimeDeriv {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (parTimeDeriv φ) :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_vecNormSq_parSpaceGrad {φ : Vec d × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous fun z => vecNormSq (parSpaceGrad φ z) := by
  have : (fun z => vecNormSq (parSpaceGrad φ z)) = fun z => ∑ i, parSpaceGrad φ z i ^ 2 :=
    funext fun z => vecNormSq_eq_sum_sq _
  rw [this]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2

theorem EnergyHyp.contDiffη_one (H : EnergyHyp U Lam a u F K η Kx T tTop δ) :
    ContDiff ℝ 1 η := H.contDiffη.of_le (by exact_mod_cast le_top)

/-- Core inequality for a fixed ramp. -/
theorem ramp_energy_core (H : EnergyHyp U Lam a u F K η Kx T tTop δ) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1)
    (hχd : ∀ t, deriv χ t ≤ 0) {t₁ : ℝ} (h1 : t₁ < tTop) (hχt : ∀ t, t₁ ≤ t → χ t = 0) :
    (∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (F (u.toFun z) * η z ^ 2 * (-deriv χ z.2)) ≤
        energyBound Lam K F u η T tTop) ∧
    ∫⁻ z in U ×ˢ Ioo T tTop,
        ENNReal.ofReal (1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) *
          η z ^ 2 * χ z.2) ≤ energyBound Lam K F u η T tTop := by
  by_cases hR : energyBound Lam K F u η T tTop = ⊤
  · rw [hR]; exact ⟨le_top, le_top⟩
  have hη1 := H.contDiffη_one
  set R := energyBound Lam K F u η T tTop with hRdef
  set S : Set (Vec d × ℝ) := U ×ˢ Ioo T tTop with hS
  set ν : Measure (Vec d × ℝ) := volume.restrict S with hν
  have hsub : S ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := prod_mono subset_rfl fun t ht =>
    ⟨by linarith [ht.1, H.hT], by linarith [ht.2, H.htTop]⟩
  -- the renormalization identity
  let φ := rampTestFunction (U := U) hη1 hχ H.compact H.subset H.vanish_x H.hT H.htTop H.hδ h1
    H.vanish_t hχt
  have hφ : φ.toFun = rampTest η χ := rfl
  have hsupp : tsupport φ.toFun ⊆ U ×ˢ Ioo T tTop := by
    rw [hφ]
    exact tsupport_rampTest_subset_Ioo H.compact H.subset H.vanish_x H.hδ h1 H.vanish_t hχt
  obtain ⟨hWi, hW0⟩ := weak_solution_renormalization_of_deriv2_bounded H.isOpen
    (ordConnected_Ioc) H.coeff u H.solution F H.contDiffF H.bdd φ
    (s := T) (t := tTop) ⟨H.hT, by linarith [H.hTt, H.htTop]⟩
    ⟨by linarith [H.hTt, H.hT], H.htTop⟩ H.hTt hsupp
  set W : Vec d × ℝ → ℝ := renormalizedIntegrand a u F φ.toFun with hWdef
  have hres := restrict_prod_Ioo_eq U T tTop
  have hWi' : Integrable W ν := by
    rw [hν, hS, hres]; exact hWi
  have hW0' : ∫ z, W z ∂ν = 0 := by
    rw [hν, hS, hres]; exact hW0
  -- a.e. facts
  have hpos : ∀ᵐ z ∂ν, 0 ≤ u.toFun z := ae_restrict_of_ae_restrict_of_subset hsub H.pos
  have hell : ∀ᵐ z ∂ν, IsEllipticMatrix 1 Lam (a z) :=
    ae_restrict_of_ae_restrict_of_subset hsub H.coeff.elliptic
  -- the error term
  let Y : Vec d × ℝ → ℝ := fun z => F (u.toFun z) *
    (2 * |η z| * |parTimeDeriv η z| + 2 * Lam * K * vecNormSq (parSpaceGrad η z))
  let Bf : Vec d × ℝ → ℝ := fun z => χ z.2 * Y z
  have hY0 : ∀ᵐ z ∂ν, 0 ≤ Y z := by
    filter_upwards [hpos, hell] with z hz he
    have hLam : 0 ≤ Lam := he.Lam_pos.le
    have hF0 := (H.Fs _ hz).1
    have := vecNormSq_nonneg (parSpaceGrad η z)
    have := H.K_nonneg
    positivity
  have hB0 : ∀ᵐ z ∂ν, 0 ≤ Bf z := by
    filter_upwards [hY0] with z hz using mul_nonneg (hχ0 _) hz
  have hBY : ∀ᵐ z ∂ν, Bf z ≤ Y z := by
    filter_upwards [hY0] with z hz
    calc Bf z = χ z.2 * Y z := rfl
      _ ≤ 1 * Y z := mul_le_mul_of_nonneg_right (hχ1 _) hz
      _ = Y z := one_mul _
  have hRY : ∫⁻ z, ENNReal.ofReal (Y z) ∂ν = R := rfl
  have hBle : ∫⁻ z, ENNReal.ofReal (Bf z) ∂ν ≤ R := by
    rw [← hRY]
    exact lintegral_mono_ae (by filter_upwards [hBY] with z hz using ENNReal.ofReal_le_ofReal hz)
  have hum : AEStronglyMeasurable u.toFun ν :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmeasB : AEStronglyMeasurable Bf ν := by
    have hFc : Continuous F := H.contDiffF.continuous
    have h1 : AEStronglyMeasurable (fun z => F (u.toFun z)) ν := hFc.comp_aestronglyMeasurable hum
    have h2 : Continuous fun z : Vec d × ℝ => 2 * |η z| * |parTimeDeriv η z| +
        2 * Lam * K * vecNormSq (parSpaceGrad η z) :=
      ((continuous_const.mul (hη1.continuous.abs)).mul
        (continuous_parTimeDeriv hη1).abs).add
        (continuous_const.mul (continuous_vecNormSq_parSpaceGrad hη1))
    have h3 : Continuous fun z : Vec d × ℝ => χ z.2 := hχ.continuous.comp continuous_snd
    exact h3.aestronglyMeasurable.mul (h1.mul h2.aestronglyMeasurable)
  have hBint : Integrable Bf ν := by
    refine ⟨hmeasB, ?_⟩
    have : ∫⁻ z, ‖Bf z‖ₑ ∂ν = ∫⁻ z, ENNReal.ofReal (Bf z) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hB0] with z hz using Real.enorm_eq_ofReal hz
    unfold HasFiniteIntegral
    rw [this]
    exact lt_of_le_of_lt hBle (lt_top_iff_ne_top.2 hR)
  -- pointwise inequality
  have hpt : ∀ᵐ z ∂ν, F (u.toFun z) * η z ^ 2 * (-deriv χ z.2) +
      1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) * η z ^ 2 * χ z.2 -
      Bf z ≤ W z := by
    filter_upwards [hpos, hell] with z hz he
    obtain ⟨hF0, hF2, hF1⟩ := H.Fs _ hz
    have := renorm_pointwise_lower he (u.grad z) (parSpaceGrad η z) (F0 := F (u.toFun z))
      (F1 := deriv F (u.toFun z)) (F2 := deriv (deriv F) (u.toFun z)) (η := η z)
      (τ := parTimeDeriv η z) (χ := χ z.2) (χ' := deriv χ z.2) hF0 hF2 H.K_nonneg (hχ0 _) hF1
    simp only [hWdef, renormalizedIntegrand, hφ, parTimeDeriv_rampTest hη1 hχ,
      parSpaceGrad_rampTest hη1 hχ, rampTest]
    simpa only [Bf, Y] using this
  have hA1 : ∀ᵐ z ∂ν, 0 ≤ F (u.toFun z) * η z ^ 2 * (-deriv χ z.2) := by
    filter_upwards [hpos] with z hz
    have := (H.Fs _ hz).1
    have := hχd z.2
    have : 0 ≤ -deriv χ z.2 := by linarith
    positivity
  have hA2 : ∀ᵐ z ∂ν, 0 ≤ 1 / 2 * deriv (deriv F) (u.toFun z) * vecNormSq (u.grad z) *
      η z ^ 2 * χ z.2 := by
    filter_upwards [hpos] with z hz
    have := (H.Fs _ hz).2.1
    have := vecNormSq_nonneg (u.grad z)
    have := hχ0 z.2
    positivity
  -- integrate
  have hsumint : Integrable (fun z => W z + Bf z) ν := hWi'.add hBint
  have hsum0 : ∀ᵐ z ∂ν, 0 ≤ W z + Bf z := by
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    linarith
  have hL : ∫⁻ z, ENNReal.ofReal (W z + Bf z) ∂ν ≤ R := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsumint hsum0, integral_add hWi' hBint, hW0',
      zero_add, ofReal_integral_eq_lintegral_ofReal hBint hB0]
    exact hBle
  constructor
  · refine le_trans (lintegral_mono_ae ?_) hL
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · refine le_trans (lintegral_mono_ae ?_) hL
    filter_upwards [hpt, hA1, hA2, hB0] with z h h1 h2 h3
    exact ENNReal.ofReal_le_ofReal (by linarith)

end PDE.Parabolic.LocalMax
