module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Core calculus estimate for the logarithmic tail bound

If `f ≥ 0` is interval integrable then
`∫ f / (ℓ + c ∫ f)² ≤ 1 / (c ℓ)`, for the primitive taken from either end of
the interval.  This is the ODE step `M' ≥ c V ⇒ ∫ V / (ℓ + M - M(t₀))² ≤ 1/(cℓ)` of
the Chebyshev argument, proved without differentiability of the primitive by
integrating the derivative of a monotone function.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace PDE.Parabolic.WeakHarnack

theorem intervalIntegrable_prefix {f : ℝ → ℝ} {a b s : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hs : s ∈ Icc a b) :
    IntervalIntegrable f volume a s :=
  hf.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)

/-- Forward version: the primitive is taken from the left endpoint. -/
theorem logTail_core_forward {f : ℝ → ℝ} {a b ℓ c : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hf0 : ∀ t, 0 ≤ f t)
    (hℓ : 0 < ℓ) (hc : 0 < c) :
    IntervalIntegrable
        (fun t => f t / (ℓ + c * ∫ s in a..t, f s) ^ 2) volume a b ∧
      ∫ t in a..b, f t / (ℓ + c * ∫ s in a..t, f s) ^ 2 ≤ 1 / (c * ℓ) := by
  set F : ℝ → ℝ := fun t => ∫ s in a..t, f s with hF
  have hFnn : ∀ t ∈ Icc a b, 0 ≤ F t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 (fun s _ => hf0 s)
  have hFmono : MonotoneOn F (Icc a b) := by
    intro s hs t ht hst
    have h1 := intervalIntegrable_prefix hab hf hs
    have h2 := intervalIntegrable_prefix hab hf ht
    have : F t - F s = ∫ r in s..t, f r := by
      simp only [hF]
      rw [← intervalIntegral.integral_interval_sub_left h2 h1]
    have h3 : 0 ≤ ∫ r in s..t, f r :=
      intervalIntegral.integral_nonneg hst (fun r _ => hf0 r)
    linarith
  have hpos : ∀ t ∈ Icc a b, 0 < ℓ + c * F t := fun t ht => by
    have := hFnn t ht; positivity
  set H : ℝ → ℝ := fun t => -(ℓ + c * F t)⁻¹ with hH
  have hHmono : MonotoneOn H (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro s hs t ht hst
    have := hFmono hs ht hst
    simp only [hH]
    have h := inv_anti₀ (hpos s hs) (by nlinarith : ℓ + c * F s ≤ ℓ + c * F t)
    linarith
  have hderiv : ∀ᵐ x ∂volume, x ∈ uIcc a b →
      deriv H x = c * (f x / (ℓ + c * F x) ^ 2) := by
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxm
    have hxI : x ∈ Icc a b := by rwa [uIcc_of_le hab] at hxm
    have hFd : HasDerivAt F (f x) x := hx hxm a (by simp [hab])
    have h1 : HasDerivAt (fun t => ℓ + c * F t) (c * f x) x :=
      (hFd.const_mul c).const_add ℓ
    have h2 : HasDerivAt H _ x := (h1.inv (hpos x hxI).ne').neg
    rw [h2.deriv]
    field_simp
  have hint : IntervalIntegrable (deriv H) volume a b :=
    hHmono.intervalIntegrable_deriv
  have hcongr' : ∀ᵐ x ∂volume, x ∈ Ι a b →
      f x / (ℓ + c * F x) ^ 2 = c⁻¹ * deriv H x := by
    filter_upwards [hderiv] with x hx hxm
    rw [hx (uIoc_subset_uIcc hxm)]
    field_simp
  have hcongr : (fun t => f t / (ℓ + c * F t) ^ 2) =ᵐ[volume.restrict (Ι a b)]
      fun t => c⁻¹ * deriv H t := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hcongr'
  have hFa : F a = 0 := by simp [hF]
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hHba : H b - H a = ℓ⁻¹ - (ℓ + c * F b)⁻¹ := by
    simp only [hH, hFa]; ring
  have hHba0 : 0 ≤ H b - H a := by
    rw [hHba, sub_nonneg]
    exact inv_anti₀ hℓ (by have := hFnn b hbI; nlinarith)
  have hmono := hHmono.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le hHba0, mem_Icc] at hmono
  have hpos' : 0 < (ℓ + c * F b)⁻¹ := inv_pos.2 (hpos b hbI)
  have hint2 : IntervalIntegrable (fun t => c⁻¹ * deriv H t) volume a b :=
    hint.const_mul _
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff] at hint2 ⊢
    exact hint2.congr hcongr.symm

  · have hI : ∫ t in a..b, f t / (ℓ + c * F t) ^ 2 = c⁻¹ * ∫ t in a..b, deriv H t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr_ae hcongr'
    rw [hI]
    have hle : ∫ t in a..b, deriv H t ≤ ℓ⁻¹ := by
      have := hmono.2
      have h2 : H b - H a ≤ ℓ⁻¹ := by rw [hHba]; linarith
      linarith
    calc c⁻¹ * ∫ t in a..b, deriv H t ≤ c⁻¹ * ℓ⁻¹ :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hc.le)
      _ = 1 / (c * ℓ) := by field_simp

/-- Backward version: the primitive is taken from the right endpoint. -/
theorem logTail_core_backward {f : ℝ → ℝ} {a b ℓ c : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hf0 : ∀ t, 0 ≤ f t)
    (hℓ : 0 < ℓ) (hc : 0 < c) :
    IntervalIntegrable
        (fun t => f t / (ℓ + c * ∫ s in t..b, f s) ^ 2) volume a b ∧
      ∫ t in a..b, f t / (ℓ + c * ∫ s in t..b, f s) ^ 2 ≤ 1 / (c * ℓ) := by
  set G : ℝ → ℝ := fun t => ∫ s in t..b, f s with hG
  have hsuffix : ∀ t ∈ Icc a b, IntervalIntegrable f volume t b := fun t ht =>
    hf.mono_set (by rw [uIcc_of_le hab, uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl)
  have hGnn : ∀ t ∈ Icc a b, 0 ≤ G t := fun t ht =>
    intervalIntegral.integral_nonneg ht.2 (fun s _ => hf0 s)
  have hGanti : AntitoneOn G (Icc a b) := by
    intro s hs t ht hst
    have h2 := hsuffix t ht
    have : G s - G t = ∫ r in s..t, f r := by
      simp only [hG]
      have h12 : IntervalIntegrable f volume s t :=
        hf.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le hst]
          exact Icc_subset_Icc hs.1 ht.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals h12 h2]
      ring
    have h3 : 0 ≤ ∫ r in s..t, f r :=
      intervalIntegral.integral_nonneg hst (fun r _ => hf0 r)
    linarith
  have hpos : ∀ t ∈ Icc a b, 0 < ℓ + c * G t := fun t ht => by
    have := hGnn t ht; positivity
  set H : ℝ → ℝ := fun t => (ℓ + c * G t)⁻¹ with hH
  have hHmono : MonotoneOn H (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro s hs t ht hst
    have := hGanti hs ht hst
    exact inv_anti₀ (hpos t ht) (by nlinarith : ℓ + c * G t ≤ ℓ + c * G s)
  have hderiv : ∀ᵐ x ∂volume, x ∈ uIcc a b →
      deriv H x = c * (f x / (ℓ + c * G x) ^ 2) := by
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxm
    have hxI : x ∈ Icc a b := by rwa [uIcc_of_le hab] at hxm
    have hFd : HasDerivAt (fun t => ∫ s in b..t, f s) (f x) x := hx hxm b (by simp [hab])
    have hGeq : G = fun t => -∫ s in b..t, f s := by
      funext t; simp only [hG]; rw [intervalIntegral.integral_symm]
    have h1 : HasDerivAt (fun t => ℓ + c * G t) (-(c * f x)) x := by
      rw [hGeq]
      simpa using (hFd.neg.const_mul c).const_add ℓ
    have h2 : HasDerivAt H _ x := h1.inv (hpos x hxI).ne'
    rw [h2.deriv]
    field_simp
  have hint : IntervalIntegrable (deriv H) volume a b :=
    hHmono.intervalIntegrable_deriv
  have hcongr' : ∀ᵐ x ∂volume, x ∈ Ι a b →
      f x / (ℓ + c * G x) ^ 2 = c⁻¹ * deriv H x := by
    filter_upwards [hderiv] with x hx hxm
    rw [hx (uIoc_subset_uIcc hxm)]
    field_simp
  have hcongr : (fun t => f t / (ℓ + c * G t) ^ 2) =ᵐ[volume.restrict (Ι a b)]
      fun t => c⁻¹ * deriv H t := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hcongr'
  have hGb : G b = 0 := by simp [hG]
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hHba : H b - H a = ℓ⁻¹ - (ℓ + c * G a)⁻¹ := by
    simp only [hH, hGb]; ring
  have hHba0 : 0 ≤ H b - H a := by
    rw [hHba, sub_nonneg]
    exact inv_anti₀ hℓ (by have := hGnn a haI; nlinarith)
  have hmono := hHmono.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le hHba0, mem_Icc] at hmono
  have hpos' : 0 < (ℓ + c * G a)⁻¹ := inv_pos.2 (hpos a haI)
  have hint2 : IntervalIntegrable (fun t => c⁻¹ * deriv H t) volume a b :=
    hint.const_mul _
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff] at hint2 ⊢
    exact hint2.congr hcongr.symm
  · have hI : ∫ t in a..b, f t / (ℓ + c * G t) ^ 2 = c⁻¹ * ∫ t in a..b, deriv H t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr_ae hcongr'
    rw [hI]
    have hle : ∫ t in a..b, deriv H t ≤ ℓ⁻¹ := by
      have := hmono.2
      have h2 : H b - H a ≤ ℓ⁻¹ := by rw [hHba]; linarith
      linarith
    calc c⁻¹ * ∫ t in a..b, deriv H t ≤ c⁻¹ * ℓ⁻¹ :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hc.le)
      _ = 1 / (c * ℓ) := by field_simp

end PDE.Parabolic.WeakHarnack
