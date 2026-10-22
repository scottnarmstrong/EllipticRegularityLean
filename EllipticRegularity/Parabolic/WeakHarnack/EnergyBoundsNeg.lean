/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyBoundsPos

/-! # Energy bounds for negative powers (cutoff vanishing at the bottom time) -/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain

variable {d : ℕ} {U : Set (Vec d)} {Λ : ℝ} {a : ParCoeffField d}
  {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ} {r ε : ℝ}

/-- **Energy bounds, negative powers `r < 0`.** The slab is `U × (lo, 0]`. -/
theorem energy_neg (hU : IsOpen U) (ha : IsParabolicCoeff 1 Λ a U (Ioc (-1 : ℝ) 0))
    (u : ParH1Function U (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSupersolution a U (Ioc (-1 : ℝ) 0) u)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ u.toFun z)
    (hΛ : 0 ≤ Λ)
    (hc : PowCutoff U Q η X T) (hr : r < 0) (hε : 0 < ε)
    (hP : Integrable (Q.indicator fun z => (u.toFun z + ε) ^ r)
      (volume.restrict (U ×ˢ Ioc (-1 : ℝ) 0)))
    {lo : ℝ} (hlo1 : -1 < lo) (hlo0 : lo < 0)
    (hlo : ∀ x τ, τ ≤ lo → η (x, τ) = 0) :
    (∀ᵐ τ ∂(volume.restrict (Ioc lo 0)),
      ∫⁻ x in U, ENNReal.ofReal (η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r) ≤
        ENNReal.ofReal ((2 * T + 2 * |r| * Λ * X / (1 - r)) *
          ∫ z in U ×ˢ Ioc (-1 : ℝ) 0, Q.indicator (fun z => (u.toFun z + ε) ^ r) z)) ∧
    ∫⁻ z in U ×ˢ Ioc lo 0,
        ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤
      ENNReal.ofReal (((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) *
        ∫ z in U ×ˢ Ioc (-1 : ℝ) 0, Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
  have hr0 : r ≠ 0 := hr.ne
  have hr1 : r < 1 := by linarith
  have hc0 : 0 < (1 - r) / 2 := by linarith
  have hr1' : 0 < 1 - r := by linarith
  have hc1 : 0 ≤ 2 * T / |r| + 2 * Λ * X / (1 - r) := by
    have := hc.hT; have := hc.hX; positivity
  have hIoc : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  obtain ⟨N, hN, hwin⟩ := window_ineq hU hIoc ha u hu hu0 hc hr1 hr0 hε hP
  have hNae : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ N := by
    rw [ae_iff]; simpa using hN
  obtain ⟨s0, hs0, hs0N⟩ := exists_notMem_null hN (show (-1 : ℝ) < lo from hlo1)
  have hs0I : s0 ∈ Ioc (-1 : ℝ) 0 := ⟨hs0.1, by linarith [hs0.2]⟩
  have hsub : ∀ s t : ℝ, s ∈ Ioc (-1 : ℝ) 0 → t ∈ Ioc (-1 : ℝ) 0 →
      U ×ˢ Ioc s t ⊆ U ×ˢ Ioc (-1 : ℝ) 0 := fun s t hs ht =>
    prod_mono subset_rfl (Ioc_subset_Ioc hs.1.le ht.2)
  have hAs0 : ∀ x : Vec d, η (x, s0) = 0 := fun x => hlo x s0 hs0.2.le
  have hzs : (∫ x in U, η (x, s0) ^ 2 * (u.toFun (x, s0) + ε) ^ r) = 0 := by simp [hAs0]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hNae] with τ hτN hτJ
    have hτI : τ ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [hτJ.1], hτJ.2⟩
    obtain ⟨hAs, hAt, hsn, htn, hineq⟩ := hwin s0 τ hs0I hτI hs0N hτN
      (by linarith [hτJ.1, hs0.2])
    rw [hzs] at hineq
    have hAnn : 0 ≤ ∫ x in U, η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r :=
      integral_nonneg_of_ae (slice_integrand_nonneg u hε htn)
    have hG : 0 ≤ ∫ z in U ×ˢ Ioc s0 τ,
        η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) :=
      integral_nonneg_of_ae (gradTerm_nonneg_ae u η hε hu0 (hsub s0 τ hs0I hτI))
    have hPW := integral_indicator_le u hu0 hε hP (hsub s0 τ hs0I hτI)
    have := (window_real_neg hr hc0 hG hAnn hPW hc1 hineq).2
    rw [← ofReal_integral_eq_lintegral_ofReal hAt (slice_integrand_nonneg u hε htn)]
    refine ENNReal.ofReal_le_ofReal (this.trans (le_of_eq ?_))
    have habs : 0 < |r| := abs_pos.2 hr0
    field_simp
  · -- exhaust `U × (lo, 0)` by `U × (s0, tₙ]`
    have hex : ∀ n : ℕ, ∃ t ∈ Ioo (max (-(1 / ((n : ℝ) + 1))) lo) 0, t ∉ N := fun n =>
      exists_notMem_null hN (max_lt (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith) hlo0)
    choose t ht htN using hex
    have htlo : ∀ n, lo < t n := fun n => (le_max_right _ _).trans_lt (ht n).1
    have htI : ∀ n, t n ∈ Ioc (-1 : ℝ) 0 := fun n => ⟨by linarith [htlo n], (ht n).2.le⟩
    have hbound : ∀ n, ∫⁻ z in U ×ˢ Ioc s0 (t n),
        ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤
        ENNReal.ofReal (((2 * T / |r| + 2 * Λ * X / (1 - r)) / ((1 - r) / 2)) *
          ∫ z in U ×ˢ Ioc (-1 : ℝ) 0, Q.indicator (fun z => (u.toFun z + ε) ^ r) z) := by
      intro n
      obtain ⟨hAs, hAt, hsn, htn, hineq⟩ := hwin s0 (t n) hs0I (htI n) hs0N (htN n)
        (by linarith [htlo n, hs0.2])
      rw [hzs] at hineq
      have hAnn : 0 ≤ ∫ x in U, η (x, t n) ^ 2 * (u.toFun (x, t n) + ε) ^ r :=
        integral_nonneg_of_ae (slice_integrand_nonneg u hε htn)
      have hG : 0 ≤ ∫ z in U ×ˢ Ioc s0 (t n),
          η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) :=
        integral_nonneg_of_ae (gradTerm_nonneg_ae u η hε hu0 (hsub s0 (t n) hs0I (htI n)))
      have hPW := integral_indicator_le u hu0 hε hP (hsub s0 (t n) hs0I (htI n))
      have := (window_real_neg hr hc0 hG hAnn hPW hc1 hineq).1
      rw [lintegral_gradTerm_eq u hc.smooth.continuous hc.le_one hc.nonneg hr1 hε hu0
        (hsub s0 (t n) hs0I (htI n))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
      linarith
    have hdir : Directed (· ⊆ ·) (fun n : ℕ => U ×ˢ Ioc s0 (t n)) := by
      intro i j
      by_cases h : t i ≤ t j
      · exact ⟨j, prod_mono subset_rfl (Ioc_subset_Ioc le_rfl h), prod_mono subset_rfl subset_rfl⟩
      · exact ⟨i, prod_mono subset_rfl subset_rfl,
          prod_mono subset_rfl (Ioc_subset_Ioc le_rfl (not_le.1 h).le)⟩
    have hcover : U ×ˢ Ioo lo 0 ⊆ ⋃ n : ℕ, U ×ˢ Ioc s0 (t n) := by
      rintro ⟨x, τ⟩ ⟨hx, hτ⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hτ.2)
      refine mem_iUnion.2 ⟨n, hx, by linarith [hs0.2, hτ.1], ?_⟩
      have h1 : -(1 / ((n : ℝ) + 1)) < t n := (le_max_left _ _).trans_lt (ht n).1
      linarith
    have hnull : (∫⁻ z in U ×ˢ ({0} : Set ℝ),
        ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))) = 0 := by
      refine setLIntegral_measure_zero _ _ ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    have hset : U ×ˢ Ioc lo 0 ⊆ U ×ˢ Ioo lo 0 ∪ U ×ˢ ({0} : Set ℝ) := by
      rintro ⟨x, τ⟩ ⟨hx, hτ1, hτ2⟩
      rcases hτ2.lt_or_eq with h | h
      · exact Or.inl ⟨hx, hτ1, h⟩
      · exact Or.inr ⟨hx, h⟩
    calc _ ≤ ∫⁻ z in U ×ˢ Ioo lo 0 ∪ U ×ˢ ({0} : Set ℝ),
          ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) :=
          lintegral_mono_set hset
      _ ≤ _ + _ := lintegral_union_le _ _ _
      _ = ∫⁻ z in U ×ˢ Ioo lo 0,
          ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) := by
          rw [hnull, add_zero]
      _ ≤ ∫⁻ z in ⋃ n : ℕ, U ×ˢ Ioc s0 (t n),
          ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) :=
          lintegral_mono_set hcover
      _ = ⨆ n : ℕ, ∫⁻ z in U ×ˢ Ioc s0 (t n),
          ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) :=
          setLIntegral_iUnion_of_directed _ hdir
      _ ≤ _ := iSup_le hbound

end PDE.Parabolic.WeakHarnack
