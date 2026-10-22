module

public import EllipticRegularity.Parabolic.WeakHarnack.LogTailCore
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Abstract logarithmic tail bound

The measure-theoretic core of the logarithmic estimate in the parabolic weak Harnack
inequality.  Let `ν` be a probability measure, `w : X → ℝ → ℝ`, `m(t) = ∫ w(·,t) dν` and
`V(t) = ∫ |w(·,t) - m(t)|² dν`.  If `m(t₂) - m(t₁) ≥ ∫_{t₁}^{t₂} (c V - K)` for all
`t₁ < t₂` in `[T₁,T₂]` outside a null set, then for `t₀ ∈ (T₁,T₂)` outside the null set and
every `ℓ > 0`,
`∫_{T₁}^{t₀} ν{w(·,t) > m(t₀) + ℓ} dt + ∫_{t₀}^{T₂} ν{w(·,t) < m(t₀) - ℓ} dt
  ≤ (4/c + 4 K (T₂-T₁)²) / ℓ`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

/-- Chebyshev's inequality for the variance around the mean. -/
theorem logTail_chebyshev {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] {g : X → ℝ} (hg : MemLp g 2 ν) {D : ℝ} (hD : 0 < D) :
    ν {x | D ≤ |g x - ∫ y, g y ∂ν|} ≤
      ENNReal.ofReal ((∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν) / D ^ 2) := by
  have hint : Integrable (fun x => (g x - ∫ y, g y ∂ν) ^ 2) ν :=
    (hg.sub (memLp_const _)).integrable_sq
  have hcheb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x - ∫ y, g y ∂ν)) hint (D ^ 2)
  have hset : {x | D ≤ |g x - ∫ y, g y ∂ν|} ⊆
      {x | D ^ 2 ≤ (g x - ∫ y, g y ∂ν) ^ 2} := fun x hx => by
    have : D ^ 2 ≤ |g x - ∫ y, g y ∂ν| ^ 2 := pow_le_pow_left₀ hD.le hx 2
    simpa [sq_abs] using this
  calc ν {x | D ≤ |g x - ∫ y, g y ∂ν|}
      ≤ ν {x | D ^ 2 ≤ (g x - ∫ y, g y ∂ν) ^ 2} := measure_mono hset
    _ = ENNReal.ofReal (ν.real {x | D ^ 2 ≤ (g x - ∫ y, g y ∂ν) ^ 2}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ (by positivity)]
        linarith

section Halves

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
  (w : X → ℝ → ℝ) {T₁ T₂ t₀ c K ℓ : ℝ} (N : Set ℝ)

/-- Right half of the tail bound, for `ℓ ≥ 2 K (T₂ - T₁)`. -/
theorem logTail_right_half (hT₁ : T₁ < t₀) (hT₂ : t₀ < T₂) (hc : 0 < c) (hK : 0 ≤ K)
    (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc T₁ T₂, t ∉ N → MemLp (fun x => w x t) 2 ν)
    (hV : IntervalIntegrable
      (fun t => ∫ x, (w x t - ∫ y, w y t ∂ν) ^ 2 ∂ν) volume T₁ T₂)
    (hdiff : ∀ t₁ ∈ Icc T₁ T₂, ∀ t₂ ∈ Icc T₁ T₂, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (w x τ - ∫ y, w y τ ∂ν) ^ 2 ∂ν - K) ≤
        (∫ x, w x t₂ ∂ν) - ∫ x, w x t₁ ∂ν)
    (ht₀ : t₀ ∉ N) (hℓ : 0 < ℓ) (hℓK : 2 * K * (T₂ - T₁) ≤ ℓ) :
    ∫⁻ t in Ioc t₀ T₂, ν {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ} ≤
      ENNReal.ofReal (2 / (c * ℓ)) := by
  set V : ℝ → ℝ := fun t => ∫ x, (w x t - ∫ y, w y t ∂ν) ^ 2 ∂ν with hVdef
  have hV0 : ∀ t, 0 ≤ V t := fun t => integral_nonneg fun x => sq_nonneg _
  have hVsub : IntervalIntegrable V volume t₀ T₂ :=
    hV.mono_set (by
      rw [uIcc_of_le hT₂.le, uIcc_of_le (hT₁.trans hT₂).le]
      exact Icc_subset_Icc hT₁.le le_rfl)
  obtain ⟨hI1, hI2⟩ := logTail_core_forward hT₂.le hVsub hV0 (half_pos hℓ) hc
  have hae : ∀ᵐ t ∂volume, t ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
  have hpt : ∀ t ∈ Ioc t₀ T₂, t ∉ N →
      ν {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ} ≤
        ENNReal.ofReal (V t / (ℓ / 2 + c * (∫ s in t₀..t, V s)) ^ 2) := by
    intro t ht htN
    have htI : t ∈ Icc T₁ T₂ := ⟨(hT₁.trans ht.1).le, ht.2⟩
    have ht₀I : t₀ ∈ Icc T₁ T₂ := ⟨hT₁.le, hT₂.le⟩
    have hd := hdiff t₀ ht₀I t htI ht₀ htN ht.1
    have hVt : IntervalIntegrable V volume t₀ t :=
      hVsub.mono_set (by
        rw [uIcc_of_le ht.1.le, uIcc_of_le hT₂.le]
        exact Icc_subset_Icc le_rfl ht.2)
    have hsplit : ∫ τ in t₀..t, (c * V τ - K) =
        c * (∫ τ in t₀..t, V τ) - K * (t - t₀) := by
      rw [intervalIntegral.integral_sub (hVt.const_mul c) intervalIntegrable_const,
        intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hg0 : 0 ≤ ∫ s in t₀..t, V s :=
      intervalIntegral.integral_nonneg ht.1.le (fun s _ => hV0 s)
    have hlen : K * (t - t₀) ≤ ℓ / 2 := by
      have : t - t₀ ≤ T₂ - T₁ := by linarith [ht.2]
      nlinarith
    have hDpos : 0 < ℓ / 2 + c * (∫ s in t₀..t, V s) := by positivity
    have hsub : {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ} ⊆
        {x | ℓ / 2 + c * (∫ s in t₀..t, V s) ≤ |w x t - ∫ y, w y t ∂ν|} := by
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hsplit] at hd
      have : ℓ / 2 + c * (∫ s in t₀..t, V s) ≤
          (∫ y, w y t ∂ν) - w x t := by
        have := hd
        linarith
      calc _ ≤ (∫ y, w y t ∂ν) - w x t := this
        _ = -(w x t - ∫ y, w y t ∂ν) := by ring
        _ ≤ _ := neg_le_abs _
    exact (measure_mono hsub).trans (logTail_chebyshev (hL2 t htI htN) hDpos)
  have hint : IntegrableOn (fun t => V t / (ℓ / 2 + c * (∫ s in t₀..t, V s)) ^ 2)
      (Ioc t₀ T₂) volume := by
    have := hI1.1
    exact this
  calc ∫⁻ t in Ioc t₀ T₂, ν {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ}
      ≤ ∫⁻ t in Ioc t₀ T₂,
          ENNReal.ofReal (V t / (ℓ / 2 + c * (∫ s in t₀..t, V s)) ^ 2) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hae] with t htN htm using hpt t htm htN
    _ = ENNReal.ofReal (∫ t in Ioc t₀ T₂,
          V t / (ℓ / 2 + c * (∫ s in t₀..t, V s)) ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => by
            have := hV0 t; positivity)).symm
    _ ≤ ENNReal.ofReal (2 / (c * ℓ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← intervalIntegral.integral_of_le hT₂.le]
        calc _ ≤ 1 / (c * (ℓ / 2)) := hI2
          _ = 2 / (c * ℓ) := by field_simp

/-- Left half of the tail bound, for `ℓ ≥ 2 K (T₂ - T₁)`. -/
theorem logTail_left_half (hT₁ : T₁ < t₀) (hT₂ : t₀ < T₂) (hc : 0 < c) (hK : 0 ≤ K)
    (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc T₁ T₂, t ∉ N → MemLp (fun x => w x t) 2 ν)
    (hV : IntervalIntegrable
      (fun t => ∫ x, (w x t - ∫ y, w y t ∂ν) ^ 2 ∂ν) volume T₁ T₂)
    (hdiff : ∀ t₁ ∈ Icc T₁ T₂, ∀ t₂ ∈ Icc T₁ T₂, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (w x τ - ∫ y, w y τ ∂ν) ^ 2 ∂ν - K) ≤
        (∫ x, w x t₂ ∂ν) - ∫ x, w x t₁ ∂ν)
    (ht₀ : t₀ ∉ N) (hℓ : 0 < ℓ) (hℓK : 2 * K * (T₂ - T₁) ≤ ℓ) :
    ∫⁻ t in Ioc T₁ t₀, ν {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t} ≤
      ENNReal.ofReal (2 / (c * ℓ)) := by
  set V : ℝ → ℝ := fun t => ∫ x, (w x t - ∫ y, w y t ∂ν) ^ 2 ∂ν with hVdef
  have hV0 : ∀ t, 0 ≤ V t := fun t => integral_nonneg fun x => sq_nonneg _
  have hVsub : IntervalIntegrable V volume T₁ t₀ :=
    hV.mono_set (by
      rw [uIcc_of_le hT₁.le, uIcc_of_le (hT₁.trans hT₂).le]
      exact Icc_subset_Icc le_rfl hT₂.le)
  obtain ⟨hI1, hI2⟩ := logTail_core_backward hT₁.le hVsub hV0 (half_pos hℓ) hc
  have hae : ∀ᵐ t ∂volume, t ∉ N := measure_eq_zero_iff_ae_notMem.1 hN
  have hae' : ∀ᵐ t ∂volume, t ≠ t₀ := by
    simp [ae_iff, measure_singleton]
  have hpt : ∀ t ∈ Ioc T₁ t₀, t ∉ N → t ≠ t₀ →
      ν {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t} ≤
        ENNReal.ofReal (V t / (ℓ / 2 + c * (∫ s in t..t₀, V s)) ^ 2) := by
    intro t ht htN htne
    have htlt : t < t₀ := lt_of_le_of_ne ht.2 htne
    have htI : t ∈ Icc T₁ T₂ := ⟨ht.1.le, htlt.le.trans hT₂.le⟩
    have ht₀I : t₀ ∈ Icc T₁ T₂ := ⟨hT₁.le, hT₂.le⟩
    have hd := hdiff t htI t₀ ht₀I htN ht₀ htlt
    have hVt : IntervalIntegrable V volume t t₀ :=
      hVsub.mono_set (by
        rw [uIcc_of_le htlt.le, uIcc_of_le hT₁.le]
        exact Icc_subset_Icc ht.1.le le_rfl)
    have hsplit : ∫ τ in t..t₀, (c * V τ - K) =
        c * (∫ τ in t..t₀, V τ) - K * (t₀ - t) := by
      rw [intervalIntegral.integral_sub (hVt.const_mul c) intervalIntegrable_const,
        intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hg0 : 0 ≤ ∫ s in t..t₀, V s :=
      intervalIntegral.integral_nonneg htlt.le (fun s _ => hV0 s)
    have hlen : K * (t₀ - t) ≤ ℓ / 2 := by
      have : t₀ - t ≤ T₂ - T₁ := by linarith [ht.1, hT₂]
      nlinarith
    have hDpos : 0 < ℓ / 2 + c * (∫ s in t..t₀, V s) := by positivity
    have hsub : {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t} ⊆
        {x | ℓ / 2 + c * (∫ s in t..t₀, V s) ≤ |w x t - ∫ y, w y t ∂ν|} := by
      intro x hx
      simp only [mem_ofPred_eq] at hx ⊢
      rw [hsplit] at hd
      have : ℓ / 2 + c * (∫ s in t..t₀, V s) ≤
          w x t - ∫ y, w y t ∂ν := by
        have := hd
        linarith
      exact this.trans (le_abs_self _)
    exact (measure_mono hsub).trans (logTail_chebyshev (hL2 t htI htN) hDpos)
  have hint : IntegrableOn (fun t => V t / (ℓ / 2 + c * (∫ s in t..t₀, V s)) ^ 2)
      (Ioc T₁ t₀) volume := hI1.1
  calc ∫⁻ t in Ioc T₁ t₀, ν {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t}
      ≤ ∫⁻ t in Ioc T₁ t₀,
          ENNReal.ofReal (V t / (ℓ / 2 + c * (∫ s in t..t₀, V s)) ^ 2) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hae, hae'] with t htN htne htm using hpt t htm htN htne
    _ = ENNReal.ofReal (∫ t in Ioc T₁ t₀,
          V t / (ℓ / 2 + c * (∫ s in t..t₀, V s)) ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => by
            have := hV0 t; positivity)).symm
    _ ≤ ENNReal.ofReal (2 / (c * ℓ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← intervalIntegral.integral_of_le hT₁.le]
        calc _ ≤ 1 / (c * (ℓ / 2)) := hI2
          _ = 2 / (c * ℓ) := by field_simp

end Halves

/-- **Abstract logarithmic tail bound.**  Let `ν` be a probability measure, `m(t) = ∫ w(·,t) dν`
and `V(t) = ∫ |w(·,t) - m(t)|² dν`.  Assume `V` is integrable on `[T₁,T₂]`,
`w(·,t) ∈ L²(ν)` for `t ∈ [T₁,T₂] \ N` (`N` null), and the integrated differential inequality
`m(t₂) - m(t₁) ≥ ∫_{t₁}^{t₂} (c V - K)` for all `t₁ < t₂` in `[T₁,T₂] \ N`.  Then for
`t₀ ∈ (T₁,T₂) \ N` and every `ℓ > 0`,
`∫_{T₁}^{t₀} ν{w(·,t) > m(t₀) + ℓ} dt + ∫_{t₀}^{T₂} ν{w(·,t) < m(t₀) - ℓ} dt
  ≤ (4/c + 4K(T₂-T₁)²)/ℓ`. -/
theorem logTail_integrated {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (w : X → ℝ → ℝ) {T₁ T₂ t₀ c K : ℝ} (N : Set ℝ)
    (hT₁ : T₁ < t₀) (hT₂ : t₀ < T₂) (hc : 0 < c) (hK : 0 ≤ K)
    (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc T₁ T₂, t ∉ N → MemLp (fun x => w x t) 2 ν)
    (hV : IntervalIntegrable
      (fun t => ∫ x, (w x t - ∫ y, w y t ∂ν) ^ 2 ∂ν) volume T₁ T₂)
    (hdiff : ∀ t₁ ∈ Icc T₁ T₂, ∀ t₂ ∈ Icc T₁ T₂, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (w x τ - ∫ y, w y τ ∂ν) ^ 2 ∂ν - K) ≤
        (∫ x, w x t₂ ∂ν) - ∫ x, w x t₁ ∂ν)
    (ht₀ : t₀ ∉ N) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫⁻ t in Ioc T₁ t₀, ν {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t}) +
        ∫⁻ t in Ioc t₀ T₂, ν {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ} ≤
      ENNReal.ofReal ((4 / c + 4 * K * (T₂ - T₁) ^ 2) / ℓ) := by
  have hL : 0 < T₂ - T₁ := by linarith
  by_cases hℓK : 2 * K * (T₂ - T₁) ≤ ℓ
  · have h1 := logTail_left_half ν w N hT₁ hT₂ hc hK hN hL2 hV hdiff ht₀ hℓ hℓK
    have h2 := logTail_right_half ν w N hT₁ hT₂ hc hK hN hL2 hV hdiff ht₀ hℓ hℓK
    calc _ ≤ ENNReal.ofReal (2 / (c * ℓ)) + ENNReal.ofReal (2 / (c * ℓ)) := add_le_add h1 h2
      _ = ENNReal.ofReal (4 / (c * ℓ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have : 4 / (c * ℓ) = (4 / c) / ℓ := by field_simp
        rw [this]
        apply div_le_div_of_nonneg_right _ hℓ.le
        have : 0 ≤ 4 * K * (T₂ - T₁) ^ 2 := by positivity
        linarith
  · push Not at hℓK
    have hb1 : ∫⁻ t in Ioc T₁ t₀, ν {x | (∫ y, w y t₀ ∂ν) + ℓ < w x t} ≤
        ENNReal.ofReal (t₀ - T₁) := by
      calc _ ≤ ∫⁻ t in Ioc T₁ t₀, (1 : ℝ≥0∞) :=
            lintegral_mono fun t => prob_le_one
        _ = ENNReal.ofReal (t₀ - T₁) := by simp
    have hb2 : ∫⁻ t in Ioc t₀ T₂, ν {x | w x t < (∫ y, w y t₀ ∂ν) - ℓ} ≤
        ENNReal.ofReal (T₂ - t₀) := by
      calc _ ≤ ∫⁻ t in Ioc t₀ T₂, (1 : ℝ≥0∞) :=
            lintegral_mono fun t => prob_le_one
        _ = ENNReal.ofReal (T₂ - t₀) := by simp
    calc _ ≤ ENNReal.ofReal (t₀ - T₁) + ENNReal.ofReal (T₂ - t₀) := add_le_add hb1 hb2
      _ = ENNReal.ofReal (T₂ - T₁) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hℓ]
        have h4 : 0 ≤ 4 / c := by positivity
        have hK' : 0 < K := by
          by_contra h
          have : K = 0 := le_antisymm (not_lt.1 h) hK
          subst this; linarith
        nlinarith [mul_pos hK' hL, mul_pos (mul_pos hK' hL) hL, mul_nonneg h4 hL.le]

end PDE.Parabolic.WeakHarnack
