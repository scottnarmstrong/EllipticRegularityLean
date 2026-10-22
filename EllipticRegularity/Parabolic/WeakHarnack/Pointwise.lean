/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.PointwiseCore

/-! # Pointwise bounds for the power and logarithm tests

Specializations of `gradPart_le_of_concave` to the profiles `κ s^r`, `-s^(-p)`, `log s`.  Writing
the renormalized supersolution inequality as
`0 ≤ ∫ -(F(v) ∂ₜφ) + gradPart …`, each bound below replaces `gradPart` by a good gradient term
and a cutoff term, which is the manuscript's energy estimate (proof of Proposition 5.13,
the display with `esssup_τ ∫ η² v^{±p}`) respectively the log inequality for `m'(t)`.
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open PDE

lemma rpow_pred_sq {v : ℝ} (hv : 0 < v) (r : ℝ) :
    (v ^ (r - 1)) ^ 2 = v ^ r * v ^ (r - 2) := by
  calc (v ^ (r - 1)) ^ 2 = v ^ (r - 1) * v ^ (r - 1) := sq _
    _ = v ^ ((r - 1) + (r - 1)) := (Real.rpow_add hv _ _).symm
    _ = v ^ (r + (r - 2)) := by ring_nf
    _ = v ^ r * v ^ (r - 2) := Real.rpow_add hv _ _

lemma rpow_half_sq {v : ℝ} (hv : 0 < v) (e : ℝ) : (v ^ (e / 2)) ^ 2 = v ^ e := by
  calc (v ^ (e / 2)) ^ 2 = v ^ (e / 2) * v ^ (e / 2) := sq _
    _ = v ^ (e / 2 + e / 2) := (Real.rpow_add hv _ _).symm
    _ = v ^ e := by ring_nf

/-- **Power profiles `κ s^r`** (`κ r > 0`, `r < 1`), at a point `v > 0`, with `φ = η²`,
`∇φ = 2η ∇η`, `m = ∇η`:
`F' A g·∇φ + F'' (A g·g) φ ≤ -(κ r (1-r)/2) η² v^(r-2) |g|² + 2 (κ r/(1-r)) Λ v^r |m|²`. -/
theorem gradPart_power_le {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {v κ r η : ℝ} (hv : 0 < v) (hκr : 0 < κ * r) (hr : r < 1) :
    gradPart (κ * r * v ^ (r - 1)) (κ * r * (r - 1) * v ^ (r - 2)) A g (η ^ 2)
        ((2 * η) • m) ≤
      -(κ * r * (1 - r) / 2) * η ^ 2 * v ^ (r - 2) * vecNormSq g +
        2 * (κ * r / (1 - r)) * v ^ r * Λ * vecNormSq m := by
  have h1r : 0 < 1 - r := by linarith
  have hx : 0 < v ^ (r - 2) := Real.rpow_pos_of_pos hv _
  have hy : 0 < v ^ r := Real.rpow_pos_of_pos hv _
  have hF2 : κ * r * (r - 1) * v ^ (r - 2) ≤ 0 := by
    have : κ * r * (r - 1) < 0 := mul_neg_of_pos_of_neg hκr (by linarith)
    exact (mul_neg_of_neg_of_pos this hx).le
  have hK0 : 0 ≤ κ * r / (1 - r) * v ^ r := by positivity
  have hK : (κ * r * v ^ (r - 1)) ^ 2 ≤
      (κ * r / (1 - r) * v ^ r) * (-(κ * r * (r - 1) * v ^ (r - 2))) := by
    apply le_of_eq
    rw [mul_pow, rpow_pred_sq hv]
    field_simp
    ring
  have h := gradPart_le_of_concave hA g m (ψ := 1) (η := η) zero_le_one hF2 hK0 hK
  simp only [one_mul] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Test `η² v^(p-1)`, `0 < p < 1`** (profile `s^p`, `F' = p v^(p-1)`, `F'' = p(p-1)v^(p-2)`):
`F' A g·∇φ + F'' (A g·g) φ ≤ -(2(1-p)/p) η² |∇(v^(p/2))|² + (2p/(1-p)) Λ v^p |∇η|²`,
where `∇(v^(p/2)) = (p/2) v^(p/2-1) g`.  Dividing the profile by `p` (take `κ = 1/p` in
`gradPart_power_le`) makes both constants bounded as `p ↓ 0`:
`-(1-p)/2 · η² v^(p-2) |g|² + 2/(1-p) · Λ v^p |∇η|²`. -/
theorem gradPart_pow_le {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {v p η : ℝ} (hv : 0 < v) (hp : 0 < p) (hp1 : p < 1) :
    gradPart (p * v ^ (p - 1)) (p * (p - 1) * v ^ (p - 2)) A g (η ^ 2) ((2 * η) • m) ≤
      -(2 * (1 - p) / p) * η ^ 2 * vecNormSq (((p / 2) * v ^ (p / 2 - 1)) • g) +
        (2 * p / (1 - p)) * Λ * v ^ p * vecNormSq m := by
  have h := gradPart_power_le hA g m (κ := 1) (η := η) hv (by linarith) hp1
  simp only [one_mul] at h
  have hsq : (v ^ (p / 2 - 1)) ^ 2 = v ^ (p - 2) := by
    have := rpow_half_sq hv (p - 2)
    rwa [show (p - 2) / 2 = p / 2 - 1 by ring] at this
  rw [vecNormSq_smul, mul_pow, hsq]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- Normalized `p ↓ 0` form of `gradPart_pow_le`: the profile `s^p / p`. -/
theorem gradPart_pow_le_normalized {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {v p η : ℝ} (hv : 0 < v) (hp : 0 < p) (hp1 : p < 1) :
    gradPart (v ^ (p - 1)) ((p - 1) * v ^ (p - 2)) A g (η ^ 2) ((2 * η) • m) ≤
      -((1 - p) / 2) * η ^ 2 * v ^ (p - 2) * vecNormSq g +
        (2 / (1 - p)) * Λ * v ^ p * vecNormSq m := by
  have h := gradPart_power_le hA g m (κ := p⁻¹) (r := p) (η := η) hv
    (by rw [inv_mul_cancel₀ hp.ne']; exact one_pos) hp1
  rw [inv_mul_cancel₀ hp.ne'] at h
  simp only [one_mul] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Test `η² v^(-p-1)`, `p > 0`** (profile `-s^(-p)`, `F' = p v^(-p-1)`,
`F'' = -p(p+1) v^(-p-2)`):
`F' A g·∇φ + F'' (A g·g) φ ≤ -(2(p+1)/p) η² |∇(v^(-p/2))|² + (2p/(p+1)) Λ v^(-p) |∇η|²`,
where `∇(v^(-p/2)) = (-p/2) v^(-p/2-1) g`. -/
theorem gradPart_negpow_le {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {v p η : ℝ} (hv : 0 < v) (hp : 0 < p) :
    gradPart (p * v ^ (-p - 1)) (-(p * (p + 1)) * v ^ (-p - 2)) A g (η ^ 2)
        ((2 * η) • m) ≤
      -(2 * (p + 1) / p) * η ^ 2 * vecNormSq (((-p / 2) * v ^ (-p / 2 - 1)) • g) +
        (2 * p / (p + 1)) * Λ * v ^ (-p) * vecNormSq m := by
  have h := gradPart_power_le hA g m (κ := -1) (r := -p) (η := η) hv (by nlinarith)
    (by linarith)
  have hsq : (v ^ (-p / 2 - 1)) ^ 2 = v ^ (-p - 2) := by
    have := rpow_half_sq hv (-p - 2)
    rwa [show (-p - 2) / 2 = -p / 2 - 1 by ring] at this
  rw [vecNormSq_smul, mul_pow, hsq]
  have hp1 : p + 1 ≠ 0 := by linarith
  have e1 : (-1 : ℝ) * -p * v ^ (-p - 1) = p * v ^ (-p - 1) := by ring
  have e2 : (-1 : ℝ) * -p * (-p - 1) * v ^ (-p - 2) = -(p * (p + 1)) * v ^ (-p - 2) := by ring
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  have e3 : 1 - -p = p + 1 := by ring
  rw [e3]
  field_simp

/-- Normalized `p ↓ 0` form of `gradPart_negpow_le`: the profile `-s^(-p) / p`. -/
theorem gradPart_negpow_le_normalized {d : ℕ} {Λ : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix 1 Λ A) (g m : Vec d) {v p η : ℝ} (hv : 0 < v) (hp : 0 < p) :
    gradPart (v ^ (-p - 1)) (-(p + 1) * v ^ (-p - 2)) A g (η ^ 2) ((2 * η) • m) ≤
      -((p + 1) / 2) * η ^ 2 * v ^ (-p - 2) * vecNormSq g +
        (2 / (p + 1)) * Λ * v ^ (-p) * vecNormSq m := by
  have h := gradPart_power_le hA g m (κ := -p⁻¹) (r := -p) (η := η) hv
    (by field_simp; norm_num) (by linarith)
  have e0 : -p⁻¹ * -p = 1 := by field_simp
  have e1 : -p⁻¹ * -p * (-p - 1) = -(p + 1) := by rw [e0]; ring
  rw [e1, e0, one_mul] at h
  have e3 : 1 - -p = p + 1 := by ring
  rw [e3] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Test `ζ² ψ / v`** (profile `log s`, `F' = 1/v`, `F'' = -1/v²`), with `φ = ψ ζ²`,
`∇φ = ψ (2ζ) ∇ζ`, `ψ ≥ 0` a time weight and `m = ∇ζ`, `∇w = v⁻¹ g` for `w = log v`:
`-F'' (A g·g) φ - F' A g·∇φ ≥ ψ ((1/2) ζ² |∇w|² - 2 Λ |∇ζ|²)`.
This is the input for `m'(t) ≥ c ∫ |∇w|² dν - C Λ`. -/
theorem neg_gradPart_log_ge {d : ℕ} {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A)
    (g m : Vec d) {v ψ ζ : ℝ} (hv : 0 < v) (hψ : 0 ≤ ψ) :
    ψ * ((1 / 2) * ζ ^ 2 * vecNormSq ((v⁻¹) • g) - 2 * Λ * vecNormSq m) ≤
      -gradPart (1 / v) (-(1 / v ^ 2)) A g (ψ * ζ ^ 2) ((ψ * (2 * ζ)) • m) := by
  have hF2 : -(1 / v ^ 2) ≤ 0 := by
    have : 0 < 1 / v ^ 2 := by positivity
    linarith
  have hK : (1 / v) ^ 2 ≤ (1 : ℝ) * (-(-(1 / v ^ 2))) := by
    rw [one_div, inv_pow, one_mul, neg_neg, one_div]
  have h := gradPart_le_of_concave hA g m (K := 1) (η := ζ) hψ hF2 zero_le_one hK
  have hn : vecNormSq (v⁻¹ • g) = (1 / v ^ 2) * vecNormSq g := by
    rw [vecNormSq_smul, inv_pow, one_div]
  rw [hn]
  have : -gradPart (1 / v) (-(1 / v ^ 2)) A g (ψ * ζ ^ 2) ((ψ * (2 * ζ)) • m) ≥
      -(ψ * ((-(1 / v ^ 2) / 2) * ζ ^ 2 * vecNormSq g + 2 * 1 * Λ * vecNormSq m)) := by
    linarith
  refine le_trans (le_of_eq ?_) this
  ring

end PDE.Parabolic.WeakHarnack
