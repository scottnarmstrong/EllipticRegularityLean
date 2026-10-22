/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyWindow

/-! # The window inequality from the slice form -/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain

variable {d : ℕ}

/-- **Window inequality.** For almost every pair of times `s < t` in `I`,
`r⁻¹ ∫_U η² v^r (s) - r⁻¹ ∫_U η² v^r (t) + ((1-r)/2) ∬_{U×(s,t]} η² v^(r-2) |∇u|²
  ≤ (2T/|r| + 2ΛX/(1-r)) ∬_{U×(s,t]} 1_Q v^r`. -/
theorem window_ineq {U : Set (Vec d)} {I : Set ℝ} {Λ : ℝ} {a : ParCoeffField d}
    (hU : IsOpen U) (hI : I.OrdConnected) (ha : IsParabolicCoeff 1 Λ a U I)
    (u : ParH1Function U I) (hu : IsParabolicWeakSupersolution a U I u)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z)
    {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ} (hc : PowCutoff U Q η X T)
    {r ε : ℝ} (hr : r < 1) (hr0 : r ≠ 0) (hε : 0 < ε)
    (hP : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r) (volume.restrict (U ×ˢ I))) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ s t : ℝ, s ∈ I → t ∈ I → s ∉ N → t ∉ N → s < t →
      IntegrableOn (fun x => η (x, s) ^ 2 * (u.toFun (x, s) + ε) ^ r) U ∧
      IntegrableOn (fun x => η (x, t) ^ 2 * (u.toFun (x, t) + ε) ^ r) U ∧
      (∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, s)) ∧
      (∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, t)) ∧
      r⁻¹ * (∫ x in U, η (x, s) ^ 2 * (u.toFun (x, s) + ε) ^ r) -
          r⁻¹ * (∫ x in U, η (x, t) ^ 2 * (u.toFun (x, t) + ε) ^ r) +
        ((1 - r) / 2) * ∫ z in U ×ˢ Ioc s t,
          η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) ≤
      (2 * T / |r| + 2 * Λ * X / (1 - r)) *
        ∫ z in U ×ˢ Ioc s t, Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
  obtain ⟨F, hF, hFL, hF1b, hF2b, hFm, hFv⟩ := exists_shifted_F (r := r) (ε := ε) hr hr0 hε
  obtain ⟨Kx, hKx, hKxU, hηK⟩ := hc.compact
  have hη1 : ContDiff ℝ 1 η := hc.smooth.of_le (by simp)
  obtain ⟨N0, hN0, hN⟩ := weak_supersolution_renormalization_slice hU hI ha u hu F hF hFL hF1b
    hF2b hFm (fun w => η w ^ 2) (hη1.pow 2) (fun z => sq_nonneg _) hKx hKxU
    (fun x hx τ => by simp [hηK x τ hx])
  have hslice : ∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ) := by
    have h : ∀ᵐ z ∂((volume.restrict U).prod (volume.restrict I)), 0 ≤ u.toFun z := by
      rw [← PDE.Parabolic.Energy.volume_restrict_prod]; exact hu0
    exact PDE.Parabolic.Energy.ae_ae_swap h
  rw [ae_restrict_iff' hI.measurableSet] at hslice
  refine ⟨N0 ∪ {τ | ¬ (τ ∈ I → ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ))}, ?_, ?_⟩
  · refine measure_union_null hN0 ?_
    rw [ae_iff] at hslice
    simpa using hslice
  intro s t hs ht hsN htN hst
  have hsN' : s ∉ N0 := fun h => hsN (Or.inl h)
  have htN' : t ∉ N0 := fun h => htN (Or.inl h)
  have hs' : ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, s) := by
    by_contra h; exact hsN (Or.inr fun h' => h (h' hs))
  have ht' : ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, t) := by
    by_contra h; exact htN (Or.inr fun h' => h (h' ht))
  obtain ⟨hint, hints, hintt, hineq⟩ := hN s t hs ht hsN' htN' hst
  have hpair : ∀ τ : ℝ, (∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ)) →
      (∫ x in U, F (u.toFun (x, τ)) * η (x, τ) ^ 2) =
        r⁻¹ * ∫ x in U, η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r := by
    intro τ hτ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hτ] with x hx
    rw [(hFv _ hx).1]; field_simp
  have hpair' : ∀ τ : ℝ, (∫ x in U, F (u.toFun (x, τ)) * (fun w : Vec d × ℝ => η w ^ 2) (x, τ)) =
      ∫ x in U, F (u.toFun (x, τ)) * η (x, τ) ^ 2 := fun τ => rfl
  have hconv : ∀ τ : ℝ, (∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ)) →
      IntegrableOn (fun x => F (u.toFun (x, τ)) * (fun w : Vec d × ℝ => η w ^ 2) (x, τ)) U →
      IntegrableOn (fun x => η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r) U := by
    intro τ hτ hi
    refine Integrable.congr (hi.const_mul r) ?_
    filter_upwards [hτ] with x hx
    simp only [(hFv _ hx).1]
    field_simp
  rw [hpair' t, hpair' s, hpair t ht', hpair s hs'] at hineq
  refine ⟨hconv s hs' hints, hconv t ht' hintt, hs', ht', ?_⟩
  have hneg : ∀ z, (F (u.toFun z) * parTimeDeriv (fun w : Vec d × ℝ => η w ^ 2) z -
        deriv (deriv F) (u.toFun z) * (fun w : Vec d × ℝ => η w ^ 2) z *
          vecDot (matVecMul (a z) (u.grad z)) (u.grad z) -
        deriv F (u.toFun z) * vecDot (matVecMul (a z) (u.grad z))
          (parSpaceGrad (fun w : Vec d × ℝ => η w ^ 2) z)) =
      -renormalizedIntegrand a u F (fun w => η w ^ 2) z := by
    intro z; unfold renormalizedIntegrand; ring
  simp_rw [hneg] at hint hineq
  rw [integral_neg] at hineq
  have hren : IntegrableOn (renormalizedIntegrand a u F (fun w => η w ^ 2)) (U ×ˢ Ioc s t) := by
    simpa using hint.neg
  have hIoc : Ioc s t ⊆ I := Ioc_subset_Icc_self.trans (hI.out hs ht)
  have hW : U ×ˢ Ioc s t ⊆ U ×ˢ I := prod_mono subset_rfl hIoc
  have hg : IntegrableOn (fun z => η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))
      (U ×ˢ Ioc s t) :=
    IntegrableOn.mono_set (t := U ×ˢ I)
      (integrable_gradTerm u hc.smooth.continuous hc.le_one hc.nonneg hr hε hu0) hW
  have hPW : IntegrableOn (Q.indicator fun z => (u.toFun z + ε) ^ r) (U ×ˢ Ioc s t) :=
    IntegrableOn.mono_set (t := U ×ˢ I) hP hW
  have hae : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc s t)),
      renormalizedIntegrand a u F (fun w => η w ^ 2) z +
          ((1 - r) / 2) * (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤
        (2 * T / |r| + 2 * Λ * X / (1 - r)) *
          Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hW hu0
    have h2 := ae_restrict_of_ae_restrict_of_subset hW ha.elliptic
    filter_upwards [h1, h2] with z hz hA
    exact ren_window_pointwise a u hc hr hr0 hε hA hz (hFv _ hz).1 (hFv _ hz).2.1
      (hFv _ hz).2.2
  have hint2 : ∫ z in U ×ˢ Ioc s t, (renormalizedIntegrand a u F (fun w => η w ^ 2) z +
          ((1 - r) / 2) * (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))) ≤
      ∫ z in U ×ˢ Ioc s t, (2 * T / |r| + 2 * Λ * X / (1 - r)) *
        Q.indicator (fun z => (u.toFun z + ε) ^ r) z :=
    integral_mono_ae (hren.add (hg.const_mul ((1 - r) / 2)))
      (hPW.const_mul (2 * T / |r| + 2 * Λ * X / (1 - r))) hae
  rw [integral_add hren (hg.const_mul _), integral_const_mul, integral_const_mul] at hint2
  linarith [hint2, hineq]

end PDE.Parabolic.WeakHarnack
