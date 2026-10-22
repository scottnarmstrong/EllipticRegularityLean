module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateMain

/-!
# Logarithmic estimate: the hypotheses of the log-tail bound for a supersolution

`log_tail_supersolution_H3` verifies all hypotheses of `logTail_integrated` (equivalently of
`posNegCyl_log_tail`) for `g = log (u + ε)`, `ν = cutoffMeasure d`, `[T₁, T₂] = [-7/8, 0]`, with
`c = logTailC d = 1 / (2 C_P(d))` and `K = Λ · logTailK0 d`, for every `ε > 0` and every weak
supersolution `u ≥ 0` of `∂ₜu - ∇·(a∇u) ≥ 0` on `B₁ × (-1, 0]` with `IsParabolicCoeff 1 Λ a`.
Constants depend only on `d` and `Λ`; `log_tail_supersolution` is the resulting tail bound.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

theorem log_tail_supersolution_H3 (d : ℕ) (Lam : ℝ) (hLam : 0 ≤ Lam) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∃ N : Set ℝ, volume N = 0 ∧
        (∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N →
          MemLp (fun x => Real.log (u.toFun (x, t) + ε)) 2 (cutoffMeasure d)) ∧
        IntervalIntegrable
          (fun t => ∫ x, (Real.log (u.toFun (x, t) + ε) -
              ∫ y, Real.log (u.toFun (y, t) + ε) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
          volume (-7 / 8) 0 ∧
        (∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
          ∫ τ in t₁..t₂, (c * ∫ x, (Real.log (u.toFun (x, τ) + ε) -
              ∫ y, Real.log (u.toFun (y, τ) + ε) ∂(cutoffMeasure d)) ^ 2
              ∂(cutoffMeasure d) - K) ≤
            (∫ x, Real.log (u.toFun (x, t₂) + ε) ∂(cutoffMeasure d)) -
              ∫ x, Real.log (u.toFun (x, t₁) + ε) ∂(cutoffMeasure d)) := by
  refine ⟨logTailC d, Lam * logTailK0 d, logTailC_pos d,
    mul_nonneg hLam (logTailK0_nonneg d), ?_⟩
  intro a ha u hu hu0 ε hε
  obtain ⟨G, hG2, hLip, hG1b, hG2b, hGmono, hGl⟩ := exists_shiftLogProfile hε
  have hGlog1 : ∀ s, 0 ≤ s → G s = Real.log (s + ε) := fun s hs => (hGl s hs).1
  have hGlog2 : ∀ s, 0 ≤ s → deriv G s = (s + ε)⁻¹ ∧
      deriv (deriv G) s = -((s + ε)⁻¹) ^ 2 := fun s hs => ⟨(hGl s hs).2.1, (hGl s hs).2.2⟩
  have hG1 : ContDiff ℝ 1 G := hG2.of_le (by norm_num)
  obtain ⟨M, hM⟩ := hG1b
  obtain ⟨L, hL⟩ := hLip
  obtain ⟨N₀, hN₀, hA⟩ := logQ_integral_le ha u hu hu0 hG2 ⟨L, hL⟩ ⟨M, hM⟩ hG2b hGmono
    hGlog2 hε
  obtain ⟨N₁, hN₁, hgood⟩ := logGood_null hG1 (M := (M : ℝ)) M.coe_nonneg hM u hu0
  have hVw := integrable_logV hG1 M.coe_nonneg hM hL u
  have hQ := integrable_logQ (Λ := Lam) hG1 (M := (M : ℝ)) hM u
  have hIcc : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∈ Ioc (-1 : ℝ) 0 := fun t ht =>
    ⟨by linarith [ht.1], ht.2⟩
  have hVae : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ioc (-1 : ℝ) 0 → τ ∉ N₁ →
      ∫ x, (Real.log (u.toFun (x, τ) + ε) -
          ∫ y, Real.log (u.toFun (y, τ) + ε) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d) =
        ∫ x, (G (u.toFun (x, τ)) - ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2
          ∂(cutoffMeasure d) := by
    refine Filter.Eventually.of_forall fun τ hI hN => ?_
    exact var_log_eq hGlog1 u (hgood τ hI hN).2
  refine ⟨N₀ ∪ N₁, measure_union_null hN₀ hN₁, ?_, ?_, ?_⟩
  · intro t ht htN
    have htN' : t ∉ N₁ := fun h => htN (Or.inr h)
    obtain ⟨⟨h, hh, -⟩, hnn⟩ := hgood t (hIcc t ht) htN'
    have hmem : MemLp (fun x => G (u.toFun (x, t))) 2 (cutoffMeasure d) := by
      refine memLp_cutoffMeasure ?_
      have := memLp_ball h (R := 1) subset_rfl
      simpa only [funext hh] using this
    exact hmem.ae_eq (log_ae_eq_G hGlog1 u hnn).symm
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hI : IntegrableOn (fun τ => ∫ x, (G (u.toFun (x, τ)) -
        ∫ y, G (u.toFun (y, τ)) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
        (Ioc (-7 / 8 : ℝ) 0) :=
      hVw.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc (by norm_num) le_rfl) le_rfl)
    refine hI.congr_fun_ae ?_
    have hae : ∀ᵐ τ ∂(volume.restrict (Ioc (-7 / 8 : ℝ) 0)), τ ∉ N₁ :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hN₁)
    filter_upwards [ae_restrict_of_ae hVae, hae, ae_restrict_mem measurableSet_Ioc] with τ h1 h2 h3
    exact (h1 ⟨by linarith [h3.1], h3.2⟩ h2).symm
  · intro t₁ ht₁ t₂ ht₂ hN1 hN2 hlt
    have hN1₀ : t₁ ∉ N₀ := fun h => hN1 (Or.inl h)
    have hN2₀ : t₂ ∉ N₀ := fun h => hN2 (Or.inl h)
    have hN1₁ : t₁ ∉ N₁ := fun h => hN1 (Or.inr h)
    have hN2₁ : t₂ ∉ N₁ := fun h => hN2 (Or.inr h)
    have hw := logDiff_w hLam u hN₁ hQ hVw hA hgood (hIcc t₁ ht₁) (hIcc t₂ ht₂) hN1₀ hN2₀ hlt
    rw [intervalIntegral.integral_of_le hlt.le,
      mean_log_eq hGlog1 u (hgood t₁ (hIcc t₁ ht₁) hN1₁).2,
      mean_log_eq hGlog1 u (hgood t₂ (hIcc t₂ ht₂) hN2₁).2]
    refine le_of_eq_of_le ?_ hw
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hae : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ N₁ :=
      measure_eq_zero_iff_ae_notMem.1 hN₁
    filter_upwards [hVae, hae] with τ h1 h2 hτ
    have hτI : τ ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [hτ.1, (hIcc t₁ ht₁).1], by
      linarith [hτ.2, (hIcc t₂ ht₂).2]⟩
    simp only [h1 hτI h2]

/-- **Logarithmic tail bound for supersolutions** (manuscript (5.21)), with the
constant depending only on `d` and `Λ`, for `ν = cutoffMeasure d`. -/
theorem log_tail_supersolution (d : ℕ) (Lam : ℝ) (hLam : 0 ≤ Lam) :
    ∃ C : ℝ, ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSupersolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ u.toFun z) →
      ∀ ε : ℝ, 0 < ε → ∃ N : Set ℝ, volume N = 0 ∧ ∀ t₀ ∈ Ioo (-7 / 8 : ℝ) 0, t₀ ∉ N →
        ∀ ℓ : ℝ, 0 < ℓ →
          (∫⁻ t in Ioc (-7 / 8 : ℝ) t₀, cutoffMeasure d
              {x | (∫ y, Real.log (u.toFun (y, t₀) + ε) ∂(cutoffMeasure d)) + ℓ <
                Real.log (u.toFun (x, t) + ε)}) +
            ∫⁻ t in Ioc t₀ 0, cutoffMeasure d
              {x | Real.log (u.toFun (x, t) + ε) <
                (∫ y, Real.log (u.toFun (y, t₀) + ε) ∂(cutoffMeasure d)) - ℓ} ≤
          ENNReal.ofReal (C / ℓ) := by
  obtain ⟨c, K, hc, hK, H⟩ := log_tail_supersolution_H3 d Lam hLam
  refine ⟨4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2, fun a ha u hu hu0 ε hε => ?_⟩
  obtain ⟨N, hN, hL2, hV, hdiff⟩ := H a ha u hu hu0 ε hε
  refine ⟨N, hN, fun t₀ ht₀ ht₀N ℓ hℓ => ?_⟩
  exact logTail_integrated (cutoffMeasure d) (fun x t => Real.log (u.toFun (x, t) + ε))
    (T₁ := -7 / 8) (T₂ := 0) N ht₀.1 ht₀.2 hc hK hN hL2 hV hdiff ht₀N hℓ

end PDE.Parabolic.WeakHarnack

