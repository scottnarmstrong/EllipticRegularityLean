module

public import EllipticRegularity.Parabolic.Cauchy.Weights.Nash
public import EllipticRegularity.Parabolic.Cauchy.Weights.Nash
public import Mathlib.Algebra.Order.Star.Real

/-!
# Time calculus for the weighted Nash estimate

The spatial weighted energy argument supplies a differential inequality for
the weighted square integral. This file proves the scalar prefactor step that
turns that inequality into the time-weighted estimate used before sending the
truncation and time shift to their limits.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

open Set
open MeasureTheory

/-- A positive time shift of size at most the elapsed time costs at most
`2^p` after pairing the growing and decaying powers. -/
theorem rpow_shift_ratio_le {τ σ p : ℝ}
    (hτ : 0 < τ) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hp : 0 ≤ p) :
    (τ + σ) ^ p * τ ^ (-p) ≤ 2 ^ p := by
  have hbase : τ + σ ≤ 2 * τ := by linarith
  have hpow := Real.rpow_le_rpow (by positivity) hbase hp
  have hscale : (2 * τ) ^ p * τ ^ (-p) = 2 ^ p := by
    rw [Real.mul_rpow (by norm_num) hτ.le]
    have hcancel : τ ^ p * τ ^ (-p) = 1 := by
      rw [← Real.rpow_add hτ, show p + (-p) = 0 by ring, Real.rpow_zero]
    rw [mul_assoc, hcancel, mul_one]
  calc
    (τ + σ) ^ p * τ ^ (-p) ≤ (2 * τ) ^ p * τ ^ (-p) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hτ.le _)
    _ = 2 ^ p := hscale

/-- Integral form of the threshold split in the Nash weighted-energy
calculation. -/
theorem weighted_square_integral_split {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q f : α → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hq : ∀ x, 0 ≤ q x) (hf : ∀ x, 0 ≤ f x)
    (hY : Integrable (fun x => Real.exp (2 * q x) * f x) μ)
    (hU : Integrable f μ)
    (hZ : Integrable (fun x => q x * Real.exp (2 * q x) * f x) μ) :
    m * (∫ x, Real.exp (2 * q x) * f x ∂μ) -
        m * Real.exp (2 * m) * (∫ x, f x ∂μ) ≤
      ∫ x, q x * Real.exp (2 * q x) * f x ∂μ := by
  have hYmul := hY.const_mul m
  have hUmul := hU.const_mul (m * Real.exp (2 * m))
  have hleft : Integrable
      (fun x => m * (Real.exp (2 * q x) * f x) -
        (m * Real.exp (2 * m)) * f x) μ := hYmul.sub hUmul
  have hpoint : ∀ x, m * (Real.exp (2 * q x) * f x) -
      (m * Real.exp (2 * m)) * f x ≤ q x * Real.exp (2 * q x) * f x := by
    intro x
    have hscalar := nashGaussianWeight_split_bound (δ := 1) (by norm_num) hm
      (hq x)
    have hscalar' : (m - q x) * Real.exp (2 * q x) ≤
        m * Real.exp (2 * m) := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hscalar' (hf x)
    nlinarith [hscaled]
  have hmono := integral_mono_ae hleft hZ (ae_of_all μ hpoint)
  calc
    m * (∫ x, Real.exp (2 * q x) * f x ∂μ) -
        m * Real.exp (2 * m) * (∫ x, f x ∂μ) =
      ∫ x, m * (Real.exp (2 * q x) * f x) -
        (m * Real.exp (2 * m)) * f x ∂μ := by
          rw [integral_sub hYmul hUmul, integral_const_mul, integral_const_mul]
    _ ≤ ∫ x, q x * Real.exp (2 * q x) * f x ∂μ := hmono

/-- A uniform derivative bound controls the increment of a differentiable
function across an interval. -/
theorem endpoint_increment_le_of_deriv_le {a b M : ℝ} {F : ℝ → ℝ}
    (hab : a < b) (hcont : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (deriv F x) x)
    (hbound : ∀ x ∈ Ioo a b, deriv F x ≤ M) :
    F b ≤ F a + M * (b - a) := by
  obtain ⟨x, hx, hslope⟩ := exists_hasDerivAt_eq_slope F (deriv F) hab hcont hderiv
  have hquot : (F b - F a) / (b - a) ≤ M := by
    rw [← hslope]
    exact hbound x hx
  have hnum := (div_le_iff₀ (sub_pos.mpr hab)).mp hquot
  linarith

/-- Integrate two successive uniform derivative bounds, as in the weighted
Nash estimate on `(0,σ)` and `(σ,h)`. -/
theorem endpoint_increment_two_phase {H σ M₀ M₁ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hσH : σ < H)
    (hcont : ContinuousOn F (Icc 0 H))
    (hderiv : ∀ x ∈ Ioo 0 H, HasDerivAt F (deriv F x) x)
    (hfast : ∀ x ∈ Ioo 0 σ, deriv F x ≤ M₀)
    (hslow : ∀ x ∈ Ioo σ H, deriv F x ≤ M₁) :
    F H ≤ F 0 + M₀ * σ + M₁ * (H - σ) := by
  have hcontFast : ContinuousOn F (Icc 0 σ) := hcont.mono (by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hσH.le⟩)
  have hcontSlow : ContinuousOn F (Icc σ H) := hcont.mono (by
    intro x hx
    exact ⟨le_trans hσ.le hx.1, hx.2⟩)
  have hderivFast : ∀ x ∈ Ioo 0 σ, HasDerivAt F (deriv F x) x := by
    intro x hx
    exact hderiv x ⟨hx.1, lt_trans hx.2 hσH⟩
  have hderivSlow : ∀ x ∈ Ioo σ H, HasDerivAt F (deriv F x) x := by
    intro x hx
    exact hderiv x ⟨lt_trans hσ hx.1, hx.2⟩
  have hfirst := endpoint_increment_le_of_deriv_le (a := 0) (b := σ)
    hσ hcontFast hderivFast hfast
  have hsecond := endpoint_increment_le_of_deriv_le (a := σ) (b := H)
    hσH hcontSlow hderivSlow hslow
  calc
    F H ≤ F σ + M₁ * (H - σ) := hsecond
    _ ≤ (F 0 + M₀ * σ) + M₁ * (H - σ) :=
      by linarith [hfirst]
    _ = F 0 + M₀ * σ + M₁ * (H - σ) := by ring

/-- Two-phase integration of the weighted Nash energy inequality. On the
short initial interval it uses the unweighted `L²` bound; after the shift it
uses the diagonal `r^(-d/2)` bound, with the shift costing only `2^(d/2)`. -/
theorem weightedEnergy_twoPhase_bound {d : ℕ} (hd : 0 < d)
    {H σ κ m C B₁ B₂ : ℝ} (hσ : 0 < σ) (hσH : σ < H)
    (hκ : κ = 1 + (d : ℝ) / 2) (hC : 0 ≤ C)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    {F U : ℝ → ℝ}
    (hcont : ContinuousOn F (Icc 0 H))
    (hderiv : ∀ r ∈ Ioo 0 H, HasDerivAt F (deriv F r) r)
    (henergy : ∀ r ∈ Ioo 0 H,
      deriv F r ≤ κ * Real.exp (2 * m) * (r + σ) ^ (κ - 1) * U r)
    (hUearly : ∀ r ∈ Ioo 0 σ, U r ≤ B₂)
    (hUlate : ∀ r ∈ Ioo σ H,
      U r ≤ C * r ^ (-(d : ℝ) / 2) * B₁) :
    F H ≤ F 0 + κ * Real.exp (2 * m) * (2 * σ) ^ (κ - 1) * B₂ * σ +
      κ * Real.exp (2 * m) * 2 ^ (κ - 1) * C * B₁ * (H - σ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hp : 0 ≤ κ - 1 := by
    rw [hκ]
    nlinarith [hdR]
  have hpEq : κ - 1 = (d : ℝ) / 2 := by rw [hκ]; ring
  have hK : 0 ≤ κ * Real.exp (2 * m) := by positivity
  have hfast : ∀ r ∈ Ioo 0 σ,
      deriv F r ≤ κ * Real.exp (2 * m) * (2 * σ) ^ (κ - 1) * B₂ := by
    intro r hr
    have hshift : r + σ ≤ 2 * σ := by nlinarith [hr.2]
    have hrshift : 0 ≤ r + σ := by linarith [hr.1, hσ]
    have hpow := Real.rpow_le_rpow hrshift hshift hp
    have hU := hUearly r hr
    have hpowU := mul_le_mul_of_nonneg_left hU
      (Real.rpow_nonneg hrshift (κ - 1))
    have hstep := mul_le_mul_of_nonneg_left hpowU hK
    have hstep₂ := mul_le_mul_of_nonneg_right hpow hB₂
    calc
      deriv F r ≤ κ * Real.exp (2 * m) * (r + σ) ^ (κ - 1) * U r :=
        henergy r ⟨hr.1, lt_trans hr.2 hσH⟩
      _ = κ * Real.exp (2 * m) * ((r + σ) ^ (κ - 1) * U r) := by ring
      _ ≤ κ * Real.exp (2 * m) * ((r + σ) ^ (κ - 1) * B₂) := hstep
      _ ≤ κ * Real.exp (2 * m) * ((2 * σ) ^ (κ - 1) * B₂) :=
        mul_le_mul_of_nonneg_left hstep₂ hK
      _ = κ * Real.exp (2 * m) * (2 * σ) ^ (κ - 1) * B₂ := by ring
  have hslow : ∀ r ∈ Ioo σ H,
      deriv F r ≤ κ * Real.exp (2 * m) * 2 ^ (κ - 1) * C * B₁ := by
    intro r hr
    have hrpos : 0 < r := lt_trans hσ hr.1
    have hU := hUlate r hr
    have hU' : U r ≤ C * r ^ (-(κ - 1)) * B₁ := by
      have hexp : -(d : ℝ) / 2 = -(κ - 1) := by rw [hpEq]; ring
      rw [hexp] at hU
      exact hU
    have hratio := rpow_shift_ratio_le hrpos hσ.le (le_of_lt hr.1) hp
    have hrshift : 0 ≤ r + σ := by linarith [hrpos, hσ]
    have hprod : (r + σ) ^ (κ - 1) * U r ≤ 2 ^ (κ - 1) * C * B₁ := by
      calc
        (r + σ) ^ (κ - 1) * U r ≤
            (r + σ) ^ (κ - 1) * (C * r ^ (-(κ - 1)) * B₁) :=
          mul_le_mul_of_nonneg_left hU' (Real.rpow_nonneg hrshift _)
        _ = ((r + σ) ^ (κ - 1) * r ^ (-(κ - 1))) * (C * B₁) := by ring
        _ ≤ 2 ^ (κ - 1) * C * B₁ := by
          calc
            _ ≤ 2 ^ (κ - 1) * (C * B₁) :=
              mul_le_mul_of_nonneg_right hratio (mul_nonneg hC hB₁)
            _ = 2 ^ (κ - 1) * C * B₁ := by ring
    calc
      deriv F r ≤ κ * Real.exp (2 * m) * (r + σ) ^ (κ - 1) * U r :=
        henergy r ⟨lt_trans hσ hr.1, hr.2⟩
      _ = κ * Real.exp (2 * m) * ((r + σ) ^ (κ - 1) * U r) := by ring
      _ ≤ κ * Real.exp (2 * m) * (2 ^ (κ - 1) * C * B₁) :=
        mul_le_mul_of_nonneg_left hprod hK
      _ = κ * Real.exp (2 * m) * 2 ^ (κ - 1) * C * B₁ := by ring
  have htwo := endpoint_increment_two_phase hσ hσH hcont hderiv hfast hslow
  calc
    F H ≤ F 0 +
        (κ * Real.exp (2 * m) * (2 * σ) ^ (κ - 1) * B₂) * σ +
        (κ * Real.exp (2 * m) * 2 ^ (κ - 1) * C * B₁) * (H - σ) := htwo
    _ = F 0 + κ * Real.exp (2 * m) * (2 * σ) ^ (κ - 1) * B₂ * σ +
        κ * Real.exp (2 * m) * 2 ^ (κ - 1) * C * B₁ * (H - σ) := by ring

/-- The Nash threshold cancellation: if the weighted energy has dissipation
`-(2δ/τ) Z` and splitting gives `Z ≥ mY - m exp(2m) U`, then multiplying by
`τ^κ` with `κ = 2δm` leaves only the unweighted square integral on the right. -/
theorem weightedEnergy_prefactor_deriv {h σ δ κ m Yd Z U : ℝ} {Y : ℝ → ℝ}
    (hτ : 0 < h + σ) (hδ : 0 < δ) (hm : κ = 2 * δ * m)
    (hY : HasDerivAt Y Yd h)
    (henergy : Yd ≤ -(2 * δ / (h + σ)) * Z)
    (hsplit : m * Y h - m * Real.exp (2 * m) * U ≤ Z) :
    deriv (fun z : ℝ => (z + σ) ^ κ * Y z) h ≤
      κ * Real.exp (2 * m) * (h + σ) ^ (κ - 1) * U := by
  have hτne : h + σ ≠ 0 := ne_of_gt hτ
  have hcoeffpos : 0 < 2 * δ / (h + σ) := by positivity
  have hcoeffneg : -(2 * δ / (h + σ)) < 0 := by
    exact neg_neg_of_pos hcoeffpos
  have hZ : (-(2 * δ / (h + σ))) * Z ≤
      (-(2 * δ / (h + σ))) * (m * Y h - m * Real.exp (2 * m) * U) :=
    mul_le_mul_of_nonpos_left hsplit hcoeffneg.le
  have hYderiv : Yd ≤
      (-(2 * δ / (h + σ))) * (m * Y h - m * Real.exp (2 * m) * U) :=
    henergy.trans hZ
  have hτderiv : HasDerivAt (fun z : ℝ => (z + σ) ^ κ)
      (κ * (h + σ) ^ (κ - 1)) h := by
    simpa using ((hasDerivAt_id h).add_const σ).rpow_const
      (p := κ) (Or.inl hτne)
  have hproduct := hτderiv.mul hY
  have hpowratio : (h + σ) ^ κ * (2 * δ / (h + σ)) =
      2 * δ * (h + σ) ^ (κ - 1) := by
    have hpow : (h + σ) ^ κ / (h + σ) = (h + σ) ^ (κ - 1) := by
      rw [show κ = (κ - 1) + 1 by ring, Real.rpow_add hτ]
      rw [Real.rpow_one]
      field_simp
      ring_nf
    calc
      (h + σ) ^ κ * (2 * δ / (h + σ)) =
          2 * δ * ((h + σ) ^ κ / (h + σ)) := by ring
      _ = 2 * δ * (h + σ) ^ (κ - 1) := by rw [hpow]
  have hcancel :
      κ * (h + σ) ^ (κ - 1) * Y h +
        (h + σ) ^ κ *
          (-(2 * δ / (h + σ)) * (m * Y h - m * Real.exp (2 * m) * U)) =
        κ * Real.exp (2 * m) * (h + σ) ^ (κ - 1) * U := by
    rw [show (h + σ) ^ κ *
        (-(2 * δ / (h + σ)) * (m * Y h - m * Real.exp (2 * m) * U)) =
        -(2 * δ * (h + σ) ^ (κ - 1)) *
          (m * Y h - m * Real.exp (2 * m) * U) by
            rw [mul_assoc, ← hpowratio]
            ring]
    rw [hm]
    ring
  change deriv ((fun z : ℝ => (z + σ) ^ κ) * Y) h ≤ _
  rw [hproduct.deriv]
  calc
    κ * (h + σ) ^ (κ - 1) * Y h + (h + σ) ^ κ * Yd ≤
        κ * (h + σ) ^ (κ - 1) * Y h +
          (h + σ) ^ κ *
            (-(2 * δ / (h + σ)) * (m * Y h - m * Real.exp (2 * m) * U) : ℝ) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hYderiv
          (Real.rpow_nonneg hτ.le κ))
    _ = κ * Real.exp (2 * m) * (h + σ) ^ (κ - 1) * U := hcancel

end PDE.Parabolic.Cauchy.Weights
