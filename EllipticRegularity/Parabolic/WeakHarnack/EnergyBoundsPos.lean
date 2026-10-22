/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyBounds

/-! # Energy bounds for positive powers (cutoff vanishing at the top time) -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : ParCoeffField d}
  {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ} {r ε : ℝ}

/-- `PW ≤ P`: restricting a nonnegative integrand to a sub-slab decreases the integral. -/
theorem integral_indicator_le {I : Set ℝ} (u : ParH1Function U I) {Q : Set (Vec d × ℝ)}
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {r ε : ℝ} (hε : 0 < ε)
    (hP : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I)))
    {W : Set (Vec d × ℝ)} (hW : W ⊆ U ×ˢ I) :
    ∫ z in W, Q.indicator (fun z => (u.toFun z + ε) ^ r) z ≤
      ∫ z in U ×ˢ I, Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
  refine setIntegral_mono_set hP ?_ (LE.le.eventuallySubset hW)
  filter_upwards [hu0] with z hz
  have : 0 < u.toFun z + ε := by linarith
  have := Real.rpow_pos_of_pos this r
  by_cases hq : z ∈ Q <;> simp [hq, this.le]

/-- **Energy bounds, positive powers.** -/
theorem energy_pos (hU : IsOpen U) (ha : IsParabolicCoeff 1 Λ a U (Ioc (-1 : ℝ) 0))
    (u : ParH1Function U (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSupersolution a U (Ioc (-1 : ℝ) 0) u)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z)
    (hΛ : 0 ≤ Λ)
    (hc : PowCutoff U Q η X T) (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hP : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r)
      (volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)))
    {lo hi : ℝ} (hlo1 : -1 < lo) (hlohi : lo < hi) (hhi0 : hi < 0)
    (hlo : ∀ x τ, τ ≤ lo → η (x, τ) = 0) (hhi : ∀ x τ, hi ≤ τ → η (x, τ) = 0) :
    (∀ᵐ τ ∂(volume.restrict (Ioo lo hi)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r) ≤
        ENNReal.ofReal ((2 * T + 2 * |r| * Λ * X / (1 - r)) *
          ∫ z in U ×ˢ Ioc (-1 : ℝ) 0, Q.indicator (fun z => (u.toFun z + ε) ^ r) z)) ∧
    ∫⁻ z in U ×ˢ Ioo lo hi,
        ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤
      ENNReal.ofReal (((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) *
        ∫ z in U ×ˢ Ioc (-1 : ℝ) 0, Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hc0 : 0 < (1 - r) / 2 := by linarith
  have hr1' : 0 < 1 - r := by linarith
  have hc1 : 0 ≤ 2 * T / |r| + 2 * Λ * X / (1 - r) := by
    have := hc.hT; have := hc.hX; positivity
  have hIoc : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  obtain ⟨N, hN, hwin⟩ := window_ineq hU hIoc ha u hu hu0 hc hr1 hr0 hε hP
  have hNae : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ N := by
    rw [ae_iff]; simpa using hN
  obtain ⟨s0, hs0, hs0N⟩ := exists_notMem_null hN (show (-1 : ℝ) < lo from hlo1)
  obtain ⟨t0, ht0, ht0N⟩ := exists_notMem_null hN (show hi < 0 from hhi0)
  have hs0I : s0 ∈ Ioc (-1 : ℝ) 0 := ⟨hs0.1, by linarith [hs0.2]⟩
  have ht0I : t0 ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [ht0.1], ht0.2.le⟩
  have hsub : ∀ s t : ℝ, s ∈ Ioc (-1 : ℝ) 0 → t ∈ Ioc (-1 : ℝ) 0 →
      U ×ˢ Ioc s t ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := fun s t hs ht =>
    prod_mono subset_rfl (Ioc_subset_Ioc hs.1.le ht.2)
  have hAt0 : ∀ x : Vec d, η (x, t0) = 0 := fun x => hhi x t0 ht0.1.le
  have hAs0 : ∀ x : Vec d, η (x, s0) = 0 := fun x => hlo x s0 hs0.2.le
  have hzt : (∫ x in U, η (x, t0) ^ 2 * (u.toFun (x, t0) + ε) ^ r) = 0 := by simp [hAt0]
  have hzs : (∫ x in U, η (x, s0) ^ 2 * (u.toFun (x, s0) + ε) ^ r) = 0 := by simp [hAs0]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hNae] with τ hτN hτJ
    have hτI : τ ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [hτJ.1], by linarith [hτJ.2]⟩
    obtain ⟨hAs, hAt, hsn, htn, hineq⟩ := hwin τ t0 hτI ht0I hτN ht0N
      (by linarith [hτJ.2, ht0.1])
    rw [hzt] at hineq
    have hAnn : 0 ≤ ∫ x in U, η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r :=
      integral_nonneg_of_ae (slice_integrand_nonneg u hε hsn)
    have hG : 0 ≤ ∫ z in U ×ˢ Ioc τ t0,
        η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) :=
      integral_nonneg_of_ae (gradTerm_nonneg_ae u η hε hu0 (hsub τ t0 hτI ht0I))
    have hPW := integral_indicator_le u hu0 hε hP (hsub τ t0 hτI ht0I)
    have := (window_real_pos hr hc0 hG hAnn hPW hc1 hineq).2
    rw [← ofReal_integral_eq_lintegral_ofReal hAs (slice_integrand_nonneg u hε hsn)]
    refine ENNReal.ofReal_le_ofReal (this.trans (le_of_eq ?_))
    have habs : 0 < |r| := abs_pos.2 hr0
    field_simp
  · have hW : U ×ˢ Ioo lo hi ⊆ U ×ˢ Ioc s0 t0 :=
      prod_mono subset_rfl (fun τ hτ => ⟨by linarith [hτ.1, hs0.2], by linarith [hτ.2, ht0.1]⟩)
    refine (lintegral_mono_set hW).trans ?_
    obtain ⟨-, -, -, -, hineq⟩ := hwin s0 t0 hs0I ht0I hs0N ht0N (by linarith [hs0.2, ht0.1, hlohi])
    rw [hzt, hzs] at hineq
    have hG : 0 ≤ ∫ z in U ×ˢ Ioc s0 t0,
        η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) :=
      integral_nonneg_of_ae (gradTerm_nonneg_ae u η hε hu0 (hsub s0 t0 hs0I ht0I))
    have hPW := integral_indicator_le u hu0 hε hP (hsub s0 t0 hs0I ht0I)
    have hAnn : (0 : ℝ) ≤ 0 := le_rfl
    have := (window_real_pos hr hc0 hG hAnn hPW hc1 (by simpa using hineq)).1
    rw [lintegral_gradTerm_eq u hc.smooth.continuous hc.le_one hc.nonneg hr1 hε hu0
      (hsub s0 t0 hs0I ht0I)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    linarith

end PDE.Parabolic.WeakHarnack
