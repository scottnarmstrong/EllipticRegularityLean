module

public import EllipticRegularity.Parabolic.Cauchy.Weights.WeightedTime
public import EllipticRegularity.Parabolic.Cauchy.Weights.TimeShift
public import EllipticRegularity.Parabolic.WeakSlice.Product
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Integrating the time weighted square norm

This is the two phase integral estimate used after the Nash threshold split.
The early and late slice bounds are inputs, so the pure scalar calculation can
be reused independently of the evolution argument that supplies them.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open MeasureTheory Set

variable {d : ℕ}

/-- Integrate the polynomial Nash time weight from an early uniform square
bound and a later diagonal decay bound. -/
theorem nashTimeWeightedMoment_bound {H σ B₁ B₂ C : ℝ} (s : ℝ)
    (hd : 0 < d) (hσ : 0 < σ) (hσH : σ < H)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂) (hC : 0 ≤ C)
    {u : Vec d × ℝ → ℝ}
    (hMomentInt : IntegrableOn
      (fun z : Vec d × ℝ =>
        (nashPositiveTimeShift σ (z.2 - s)) ^ (((d : ℝ) / 2)) * u z ^ 2)
      ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)))
    (hSliceInt : ∀ t ∈ Icc s (s + H),
      Integrable (fun x : Vec d => u (x, t) ^ 2) volume)
    (hEarly : ∀ᵐ t ∂(volume.restrict (Ioc s (s + σ))),
      ∫ x : Vec d, u (x, t) ^ 2 ≤ B₂)
    (hLate : ∀ᵐ t ∂(volume.restrict (Ioc (s + σ) (s + H))),
      ∫ x : Vec d, u (x, t) ^ 2 ≤
        C * (t - s) ^ (-(d : ℝ) / 2) * B₁) :
    IntegrableOn
        (fun z : Vec d × ℝ =>
          (nashPositiveTimeShift σ (z.2 - s)) ^ ((d : ℝ) / 2) * u z ^ 2)
        ((univ : Set (Vec d)) ×ˢ Ioc s (s + H)) ∧
    ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s (s + H),
      (nashPositiveTimeShift σ (z.2 - s)) ^ (((d : ℝ) / 2)) * u z ^ 2 ≤
      (2 * σ) ^ ((d : ℝ) / 2) * B₂ * σ +
        2 ^ ((d : ℝ) / 2) * C * B₁ * (H - σ) := by
  let J : Set ℝ := Ioc s (s + H)
  let J₀ : Set ℝ := Ioc s (s + σ)
  let J₁ : Set ℝ := Ioc (s + σ) (s + H)
  let V : ℝ → ℝ := fun t =>
    ∫ x : Vec d,
      (nashPositiveTimeShift σ (t - s)) ^ ((d : ℝ) / 2) * u (x, t) ^ 2
  let p : ℝ := (d : ℝ) / 2
  let B₀ : ℝ := (2 * σ) ^ p * B₂
  let Bmid : ℝ := 2 ^ p * C * B₁
  have hpnonneg : 0 ≤ p := by dsimp [p]; positivity
  have hmeasure := PDE.Parabolic.WeakSlice.integral_prod_slices
    (U := (univ : Set (Vec d))) (J := J) (f := fun z : Vec d × ℝ =>
      (nashPositiveTimeShift σ (z.2 - s)) ^ p * u z ^ 2) (by
        simpa [J, p] using hMomentInt)
  have hVint : IntegrableOn V J := by simpa [V, J] using hmeasure.1
  have hVfubini : ∫ z in (univ : Set (Vec d)) ×ˢ J,
      (nashPositiveTimeShift σ (z.2 - s)) ^ p * u z ^ 2 =
        ∫ t in J, V t := by simpa [V, J] using hmeasure.2
  have hJunion : J₀ ∪ J₁ = J := by
    ext t
    simp only [mem_union]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans (by linarith : s + σ ≤ s + H)⟩
      · exact ⟨lt_trans (by linarith : s < s + σ) h.1, h.2⟩
    · rintro ⟨hs, ht⟩
      by_cases hσt : t ≤ s + σ
      · exact Or.inl ⟨hs, hσt⟩
      · exact Or.inr ⟨lt_of_not_ge hσt, ht⟩
  have hJdisjoint : Disjoint J₀ J₁ := by
    rw [Set.disjoint_left]
    intro t ht₀ ht₁
    exact (not_lt_of_ge ht₀.2) ht₁.1
  have hJ₀int : IntegrableOn V J₀ := by
    apply hVint.mono_set
    intro t ht
    exact ⟨ht.1, ht.2.trans (by linarith : s + σ ≤ s + H)⟩
  have hJ₁int : IntegrableOn V J₁ := by
    apply hVint.mono_set
    intro t ht
    exact ⟨lt_trans (by linarith : s < s + σ) ht.1, ht.2⟩
  have hEarly' : ∀ᵐ t ∂(volume.restrict J₀), V t ≤ B₀ := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hEarly] with t ht
    intro htmem
    let τ := nashPositiveTimeShift σ (t - s)
    have hτeq : τ = t - s + σ := by
      dsimp [τ]
      exact nashPositiveTimeShift_eq_add hσ (sub_nonneg.mpr (le_of_lt htmem.1))
    have hτpos : 0 < τ := by
      rw [hτeq]
      have hr : 0 < t - s := by linarith [htmem.1]
      exact add_pos hr hσ
    have hτle : τ ≤ 2 * σ := by
      rw [hτeq]
      linarith [htmem.2, htmem.1]
    have htJ : t ∈ Icc s (s + H) :=
      ⟨le_of_lt htmem.1, le_trans htmem.2 (by linarith [hσH])⟩
    have hUint : Integrable (fun x : Vec d => u (x, t) ^ 2) volume := hSliceInt t htJ
    have hU0 : 0 ≤ ∫ x : Vec d, u (x, t) ^ 2 := by
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun x => sq_nonneg _
    have hVeq : V t = τ ^ p * ∫ x : Vec d, u (x, t) ^ 2 := by
      dsimp [V, τ]
      rw [integral_const_mul]
    have hpow : τ ^ p ≤ (2 * σ) ^ p :=
      Real.rpow_le_rpow hτpos.le hτle hpnonneg
    have hUbound : ∫ x : Vec d, u (x, t) ^ 2 ≤ B₂ := ht htmem
    rw [hVeq]
    dsimp [B₀]
    calc
      τ ^ p * ∫ x : Vec d, u (x, t) ^ 2 ≤
          (2 * σ) ^ p * ∫ x : Vec d, u (x, t) ^ 2 :=
        mul_le_mul_of_nonneg_right hpow hU0
      _ ≤ (2 * σ) ^ p * B₂ :=
        mul_le_mul_of_nonneg_left hUbound (Real.rpow_nonneg (by positivity) p)
  have hLate' : ∀ᵐ t ∂(volume.restrict J₁), V t ≤ Bmid := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hLate] with t ht
    intro htmem
    let τ := nashPositiveTimeShift σ (t - s)
    let r := t - s
    have hrpos : 0 < r := by
      dsimp [r]
      linarith [htmem.1, hσ]
    have hτeq : τ = r + σ := by
      dsimp [τ, r]
      exact nashPositiveTimeShift_eq_add hσ hrpos.le
    have hrσ : σ ≤ r := by dsimp [r]; linarith [htmem.1]
    have hτpos : 0 < τ := by rw [hτeq]; positivity
    have hratio := rpow_shift_ratio_le hrpos hσ.le hrσ hpnonneg
    have htJ : t ∈ Icc s (s + H) := ⟨by linarith [htmem.1], htmem.2⟩
    have hUint : Integrable (fun x : Vec d => u (x, t) ^ 2) volume := hSliceInt t htJ
    have hU0 : 0 ≤ ∫ x : Vec d, u (x, t) ^ 2 := by
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun x => sq_nonneg _
    have hVeq : V t = τ ^ p * ∫ x : Vec d, u (x, t) ^ 2 := by
      dsimp [V, τ]
      rw [integral_const_mul]
    have hUbound : ∫ x : Vec d, u (x, t) ^ 2 ≤
        C * r ^ (-p) * B₁ := by
      have h := ht htmem
      have hexp : -(d : ℝ) / 2 = -p := by dsimp [p]; ring
      rw [hexp] at h
      simpa [r] using h
    rw [hVeq, hτeq]
    dsimp [Bmid]
    calc
      (r + σ) ^ p * ∫ x : Vec d, u (x, t) ^ 2 ≤
          (r + σ) ^ p * (C * r ^ (-p) * B₁) :=
        mul_le_mul_of_nonneg_left hUbound (Real.rpow_nonneg (by positivity) p)
      _ = ((r + σ) ^ p * r ^ (-p)) * (C * B₁) := by ring
      _ ≤ 2 ^ p * (C * B₁) :=
        mul_le_mul_of_nonneg_right hratio (mul_nonneg hC hB₁)
      _ = 2 ^ p * C * B₁ := by ring
  have hV0int : IntegrableOn (fun _ : ℝ => B₀) J₀ := by
    exact integrableOn_const (C := B₀) (s := J₀)
      (μ := volume) (measure_Ioc_lt_top (μ := volume)).ne
  have hV1int : IntegrableOn (fun _ : ℝ => Bmid) J₁ := by
    exact integrableOn_const (C := Bmid) (s := J₁)
      (μ := volume) (measure_Ioc_lt_top (μ := volume)).ne
  have hI0 : (∫ t in J₀, V t ∂volume) ≤ B₀ * σ := by
    have hmono := integral_mono_ae hJ₀int hV0int hEarly'
    calc
      (∫ t in J₀, V t ∂volume) ≤ ∫ t in J₀, B₀ ∂volume := hmono
      _ = B₀ * σ := by
        rw [setIntegral_const]
        have hlen : volume.real J₀ = σ := by
          rw [Measure.real_def]
          dsimp [J₀]
          rw [Real.volume_Ioc, show (s + σ) - s = σ by ring]
          exact ENNReal.toReal_ofReal hσ.le
        rw [hlen, smul_eq_mul]
        ring
  have hI1 : (∫ t in J₁, V t ∂volume) ≤ Bmid * (H - σ) := by
    have hmono := integral_mono_ae hJ₁int hV1int hLate'
    calc
      (∫ t in J₁, V t ∂volume) ≤ ∫ t in J₁, Bmid ∂volume := hmono
      _ = Bmid * (H - σ) := by
        rw [setIntegral_const]
        have hlen : (s + H) - (s + σ) = H - σ := by ring
        have hmeasure : volume.real J₁ = H - σ := by
          rw [Measure.real_def]
          dsimp [J₁]
          rw [Real.volume_Ioc, hlen]
          exact ENNReal.toReal_ofReal (sub_nonneg.mpr hσH.le)
        rw [hmeasure, smul_eq_mul]
        ring
  have hI01 : (∫ t in J₀ ∪ J₁, V t ∂volume) =
      (∫ t in J₀, V t ∂volume) + ∫ t in J₁, V t ∂volume :=
    setIntegral_union (μ := volume) hJdisjoint measurableSet_Ioc hJ₀int hJ₁int
  have hsplit : (∫ t in J, V t ∂volume) =
      (∫ t in J₀, V t ∂volume) + ∫ t in J₁, V t ∂volume := by
    rw [← hJunion]
    exact hI01
  have hsum : (∫ t in J, V t ∂volume) ≤ B₀ * σ + Bmid * (H - σ) := by
    rw [hsplit]
    exact add_le_add hI0 hI1
  refine ⟨hMomentInt, ?_⟩
  rw [hVfubini]
  simpa [J, J₀, J₁, V, p, B₀, Bmid] using hsum

end PDE.Parabolic.Cauchy.Weights
