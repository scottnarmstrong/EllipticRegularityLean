/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergySlice

/-! # Energy bounds: the `esssup` term and the gradient term

From the window inequality (`window_ineq`) we derive, for a cutoff `η` vanishing at the top time
(positive powers, `0 < r < 1`) respectively at the bottom time (negative powers, `r < 0`), the two
bounds feeding the parabolic Sobolev inequality:

* for a.e. `τ`, `∫_U η² v^r (τ) ≤ |r| c₁ P`,
* `∬ η² v^(r-2) |∇u|² ≤ (c₁/c₀) P`,

where `P = ∬_Q v^r`, `c₀ = (1-r)/2`, `c₁ = 2T/|r| + 2ΛX/(1-r)`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain

variable {d : ℕ}

theorem exists_notMem_null {N : Set ℝ} (hN : volume N = 0) {x y : ℝ} (hxy : x < y) :
    ∃ t ∈ Ioo x y, t ∉ N := by
  by_contra h
  push Not at h
  have : Ioo x y ⊆ N := h
  have h1 := measure_mono (μ := volume) this
  rw [hN, Real.volume_Ioo] at h1
  have : ENNReal.ofReal (y - x) = 0 := nonpos_iff_eq_zero.1 h1
  rw [ENNReal.ofReal_eq_zero] at this
  linarith

/-- Pure-real consequence of the window inequality, positive powers (`A t = 0`). -/
theorem window_real_pos {r c0 c1 As G PW P : ℝ} (hr : 0 < r) (hc0 : 0 < c0) (hG : 0 ≤ G)
    (hAs : 0 ≤ As) (hPW : PW ≤ P) (hc1 : 0 ≤ c1)
    (h : r⁻¹ * As - r⁻¹ * 0 + c0 * G ≤ c1 * PW) :
    c0 * G ≤ c1 * P ∧ As ≤ |r| * c1 * P := by
  have h1 : c1 * PW ≤ c1 * P := mul_le_mul_of_nonneg_left hPW hc1
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have h2 : 0 ≤ r⁻¹ * As := mul_nonneg hri.le hAs
  have h3 : 0 ≤ c0 * G := mul_nonneg hc0.le hG
  refine ⟨by linarith, ?_⟩
  have h4 : r⁻¹ * As ≤ c1 * P := by linarith
  rw [abs_of_pos hr]
  have hr0 : r ≠ 0 := hr.ne'
  calc As = r * (r⁻¹ * As) := by field_simp
    _ ≤ r * (c1 * P) := mul_le_mul_of_nonneg_left h4 hr.le
    _ = _ := by ring

/-- Pure-real consequence of the window inequality, negative powers (`A s = 0`). -/
theorem window_real_neg {r c0 c1 At G PW P : ℝ} (hr : r < 0) (hc0 : 0 < c0) (hG : 0 ≤ G)
    (hAt : 0 ≤ At) (hPW : PW ≤ P) (hc1 : 0 ≤ c1)
    (h : r⁻¹ * 0 - r⁻¹ * At + c0 * G ≤ c1 * PW) :
    c0 * G ≤ c1 * P ∧ At ≤ |r| * c1 * P := by
  have h1 : c1 * PW ≤ c1 * P := mul_le_mul_of_nonneg_left hPW hc1
  have hri : 0 < -r⁻¹ := neg_pos.2 (inv_lt_zero.2 hr)
  have h2 : 0 ≤ -r⁻¹ * At := mul_nonneg hri.le hAt
  have h3 : 0 ≤ c0 * G := mul_nonneg hc0.le hG
  refine ⟨by linarith, ?_⟩
  have h4 : -r⁻¹ * At ≤ c1 * P := by linarith
  rw [abs_of_neg hr]
  have hr0 : r ≠ 0 := hr.ne
  calc At = -r * (-r⁻¹ * At) := by field_simp
    _ ≤ -r * (c1 * P) := mul_le_mul_of_nonneg_left h4 (neg_nonneg.2 hr.le)
    _ = _ := by ring

section Setting

variable {U : Set (Vec d)} {Λ : ℝ} {a : ParCoeffField d}
  {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ} {r ε : ℝ}

/-- The lintegral of the (nonnegative) gradient term over a slab inside `U × I`. -/
theorem lintegral_gradTerm_eq {I : Set ℝ} (u : ParH1Function U I) {η : Vec d × ℝ → ℝ}
    (hη : Continuous η) (hη1 : ∀ z, η z ≤ 1) (hη0 : ∀ z, 0 ≤ η z) (hr : r < 1) (hε : 0 < ε)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) {W : Set (Vec d × ℝ)}
    (hW : W ⊆ U ×ˢ I) :
    ∫⁻ z in W, ENNReal.ofReal (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) =
      ENNReal.ofReal (∫ z in W, η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) := by
  have hint : IntegrableOn (fun z => η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) W :=
    IntegrableOn.mono_set (t := U ×ˢ I) (integrable_gradTerm u hη hη1 hη0 hr hε hu0) hW
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hW hu0] with z hz
  have : 0 < u.toFun z + ε := by linarith
  have := Real.rpow_pos_of_pos this (r - 2)
  have := vecNormSq_nonneg (u.grad z)
  positivity

/-- Nonnegativity of the slice integrand. -/
theorem slice_integrand_nonneg {I : Set ℝ} (u : ParH1Function U I) {η : Vec d × ℝ → ℝ}
    {r ε : ℝ} (hε : 0 < ε) {τ : ℝ}
    (hτ : ∀ᵐ x ∂(volume.restrict U), 0 ≤ u.toFun (x, τ)) :
    ∀ᵐ x ∂(volume.restrict U), 0 ≤ η (x, τ) ^ 2 * (u.toFun (x, τ) + ε) ^ r := by
  filter_upwards [hτ] with x hx
  have : 0 < u.toFun (x, τ) + ε := by linarith
  have := Real.rpow_pos_of_pos this r
  positivity

/-- Nonnegativity of the gradient term, a.e. -/
theorem gradTerm_nonneg_ae {I : Set ℝ} (u : ParH1Function U I) (η : Vec d × ℝ → ℝ) {r ε : ℝ}
    (hε : 0 < ε) (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z)
    {W : Set (Vec d × ℝ)} (hW : W ⊆ U ×ˢ I) :
    ∀ᵐ z ∂(volume.restrict W),
      0 ≤ η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hW hu0] with z hz
  have : 0 < u.toFun z + ε := by linarith
  have := Real.rpow_pos_of_pos this (r - 2)
  have := vecNormSq_nonneg (u.grad z)
  positivity

end Setting

end PDE.Parabolic.WeakHarnack
