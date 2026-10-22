module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The real-number bookkeeping of the decay lemma

Pure real arithmetic: from the four inequalities of Steps 1-3 of Lemma 4.35
(energy, duality, gradient bound, oscillation) to the final power-law bound.
-/

@[expose] public section

namespace PDE.Ch4GreenDecay

open Real

/-- The dimensional constant of the decay lemma. -/
noncomputable def decayConst (d : ℕ) (Cp ω : ℝ) : ℝ :=
  2 * Real.sqrt ((2 : ℝ) ^ d) * Cp ^ 2 * 2 ^ d / (Real.sqrt ω * Real.sqrt ((2 : ℝ) ^ d - 1))

theorem rpow_aux {d : ℕ} {r β : ℝ} (hr : 0 < r) (hβ1 : β ≤ 1) :
    (r / 2) ^ (-β) * (r / 2) * ((r / 2) ^ d)⁻¹ * r ≤ 2 ^ d * r ^ (2 - β - (d : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpow : ((r / 2) ^ d)⁻¹ = 2 ^ d * (r ^ d)⁻¹ := by
    rw [div_pow, inv_div]; field_simp
  have hb : (r / 2) ^ (-β) = r ^ (-β) * 2 ^ β := by
    rw [Real.div_rpow hr.le h2.le, Real.rpow_neg h2.le, div_eq_mul_inv, inv_inv]
  have hr2 : r ^ (2 - β - (d : ℝ)) = r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹) := by
    have : (2 - β - (d : ℝ)) = (-β) + ((2 : ℝ) + (-(d : ℝ))) := by ring
    rw [this, Real.rpow_add hr, Real.rpow_add hr, Real.rpow_neg hr.le (d : ℝ),
      Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2b : (2 : ℝ) ^ β ≤ 2 := by
    calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
      _ = 2 := Real.rpow_one 2
  rw [hb, hpow, hr2]
  have hnn : 0 ≤ r ^ (-β) * (2 ^ d * (r ^ d)⁻¹ * r ^ 2) := by positivity
  have : r ^ (-β) * 2 ^ β * (r / 2) * (2 ^ d * (r ^ d)⁻¹) * r =
      (2 ^ β / 2) * (2 ^ d * (r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹))) := by
    field_simp
  rw [this]
  have hx : 0 ≤ (2 : ℝ) ^ d * (r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹)) := by positivity
  calc (2 ^ β / 2) * (2 ^ d * (r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹)))
      ≤ 1 * (2 ^ d * (r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹))) := by
        refine mul_le_mul_of_nonneg_right ?_ hx
        rw [div_le_one h2]; exact h2b
    _ = 2 ^ d * (r ^ (-β) * (r ^ 2 * (r ^ d)⁻¹)) := one_mul _

/-- **The real-number core of the decay lemma.** -/
theorem decay_algebra {d : ℕ} (hd : 0 < d) {ω Λ Cs β r Cp nG nf n1 nR Q Iρ : ℝ}
    (hω : 0 < ω) (hΛ : 1 ≤ Λ) (hβ1 : β ≤ 1) (hCs : 0 ≤ Cs) (hr : 0 < r)
    (hCp : 0 < Cp) (hnG : 0 ≤ nG) (hnf : 0 ≤ nf) (hnR : 0 ≤ nR)
    (hIρ : 0 ≤ Iρ)
    (h1 : nG ^ 2 ≤ nf * n1)
    (h2 : n1 ^ 2 ≤ 4 * Λ * (ω * 2 ^ d) * Q ^ 2)
    (hQ : Q = Cs * (r / 2) ^ (-β) * Real.sqrt (Iρ / (ω * (r / 2) ^ d)))
    (h4 : Iρ ≤ (Cp * (r / 2)) ^ 2 * nR ^ 2)
    (h5 : nR ≤ Cp * r * nG) :
    nG / Real.sqrt (ω * (r ^ d - (r / 2) ^ d)) ≤
      decayConst d Cp ω * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ)) * nf := by
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hΛ0 : 0 < Λ := by linarith
  have hVρ : 0 < ω * ρ ^ d := by positivity
  set Xρ : ℝ := Real.sqrt (ω * ρ ^ d) with hXρ
  have hXρ0 : 0 < Xρ := Real.sqrt_pos.2 hVρ
  have hXρsq : Xρ ^ 2 = ω * ρ ^ d := Real.sq_sqrt hVρ.le
  have h2d : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h2d1 : 0 < (2 : ℝ) ^ d - 1 := by linarith
  set t : ℝ := Real.sqrt ((2 : ℝ) ^ d) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 (by positivity)
  have htsq : t ^ 2 = 2 ^ d := Real.sq_sqrt (by positivity)
  set s2 : ℝ := Real.sqrt ((2 : ℝ) ^ d - 1) with hs2
  have hs20 : 0 < s2 := Real.sqrt_pos.2 h2d1
  set sω : ℝ := Real.sqrt ω with hsω
  have hsω0 : 0 < sω := Real.sqrt_pos.2 hω
  have hsωsq : sω ^ 2 = ω := Real.sq_sqrt hω.le
  -- the annulus volume
  have hVA : ω * (r ^ d - ρ ^ d) = (ω * ρ ^ d) * (2 ^ d - 1) := by
    have : r = 2 * ρ := by rw [hρdef]; ring
    rw [this, mul_pow]; ring
  have hsqrtVA : Real.sqrt (ω * (r ^ d - ρ ^ d)) = Xρ * s2 := by
    rw [hVA, Real.sqrt_mul hVρ.le]
  -- Step a: `n1 ≤ 2 sqrt(Λ V₂) Q`
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hsqΛ : 0 ≤ Real.sqrt (Λ * (ω * 2 ^ d)) := Real.sqrt_nonneg _
  have hsqΛsq : Real.sqrt (Λ * (ω * 2 ^ d)) ^ 2 = Λ * (ω * 2 ^ d) :=
    Real.sq_sqrt (by positivity)
  have ha : n1 ≤ 2 * Real.sqrt (Λ * (ω * 2 ^ d)) * Q := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 ≤ 2 * Real.sqrt (Λ * (ω * 2 ^ d)) * Q := by positivity
    have : (2 * Real.sqrt (Λ * (ω * 2 ^ d)) * Q) ^ 2 < n1 ^ 2 :=
      pow_lt_pow_left₀ hcon hpos two_ne_zero
    have e : (2 * Real.sqrt (Λ * (ω * 2 ^ d)) * Q) ^ 2 = 4 * Λ * (ω * 2 ^ d) * Q ^ 2 := by
      rw [mul_pow, mul_pow, hsqΛsq]; ring
    linarith
  -- Step b: `Q ≤ Cs ρ^{-β} Cp ρ nR / Xρ`
  have hb : Q ≤ Cs * ρ ^ (-β) * (Cp * ρ * nR) / Xρ := by
    have hsq : Real.sqrt (Iρ / (ω * ρ ^ d)) ≤ Cp * ρ * nR / Xρ := by
      rw [Real.sqrt_div hIρ, ← hXρ]
      refine div_le_div_of_nonneg_right ?_ hXρ0.le
      calc Real.sqrt Iρ ≤ Real.sqrt ((Cp * ρ * nR) ^ 2) := by
            apply Real.sqrt_le_sqrt
            calc Iρ ≤ (Cp * ρ) ^ 2 * nR ^ 2 := h4
              _ = (Cp * ρ * nR) ^ 2 := by ring
        _ = Cp * ρ * nR := Real.sqrt_sq (by positivity)
    calc Q = (Cs * ρ ^ (-β)) * Real.sqrt (Iρ / (ω * ρ ^ d)) := hQ
      _ ≤ (Cs * ρ ^ (-β)) * (Cp * ρ * nR / Xρ) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Cs * ρ ^ (-β) * (Cp * ρ * nR) / Xρ := by ring
  -- Step c: `n1 ≤ M nG`
  set M : ℝ := 2 * Real.sqrt (Λ * (ω * 2 ^ d)) * (Cs * ρ ^ (-β) * (Cp * ρ * (Cp * r)) / Xρ)
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hc : n1 ≤ M * nG := by
    have hQ2 : Q ≤ Cs * ρ ^ (-β) * (Cp * ρ * (Cp * r * nG)) / Xρ := by
      refine hb.trans ?_
      refine div_le_div_of_nonneg_right ?_ hXρ0.le
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    calc n1 ≤ 2 * Real.sqrt (Λ * (ω * 2 ^ d)) * Q := ha
      _ ≤ 2 * Real.sqrt (Λ * (ω * 2 ^ d)) *
            (Cs * ρ ^ (-β) * (Cp * ρ * (Cp * r * nG)) / Xρ) :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = M * nG := by rw [hM]; ring
  -- Step d: `nG ≤ M nf`
  have hd' : nG ≤ M * nf := by
    rcases eq_or_lt_of_le hnG with h0 | hpos
    · rw [← h0]; positivity
    · by_contra hcon
      push Not at hcon
      have : nG ^ 2 ≤ nf * (M * nG) := h1.trans (mul_le_mul_of_nonneg_left hc hnf)
      have := mul_lt_mul_of_pos_right hcon hpos
      linarith
  -- Step e: division by `sqrt |A_r|`
  rw [hsqrtVA]
  have hden : 0 < Xρ * s2 := mul_pos hXρ0 hs20
  rw [div_le_iff₀ hden]
  have hMnf : M * nf / (Xρ * s2) ≤ decayConst d Cp ω * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ)) * nf := by
    have hMeq : M / (Xρ * s2) =
        decayConst d Cp ω / 2 ^ d * Cs * Real.sqrt Λ * (ρ ^ (-β) * ρ * (ρ ^ d)⁻¹ * r) := by
      have hsqΛ' : Real.sqrt (Λ * (ω * 2 ^ d)) = Real.sqrt Λ * (sω * t) := by
        rw [Real.sqrt_mul hΛ0.le, Real.sqrt_mul hω.le]
      have hdc : decayConst d Cp ω = 2 * t * Cp ^ 2 * 2 ^ d / (sω * s2) := rfl
      have hXρ' : Xρ ^ 2 = sω ^ 2 * ρ ^ d := by rw [hXρsq, hsωsq]
      rw [hM, hsqΛ', hdc]
      field_simp
      rw [hXρ']
      ring
    have hbound := rpow_aux (d := d) hr hβ1
    have hfac : 0 ≤ decayConst d Cp ω / 2 ^ d * Cs * Real.sqrt Λ := by
      unfold decayConst; positivity
    calc M * nf / (Xρ * s2) = (M / (Xρ * s2)) * nf := by ring
      _ = decayConst d Cp ω / 2 ^ d * Cs * Real.sqrt Λ * (ρ ^ (-β) * ρ * (ρ ^ d)⁻¹ * r) * nf := by
          rw [hMeq]
      _ ≤ decayConst d Cp ω / 2 ^ d * Cs * Real.sqrt Λ * (2 ^ d * r ^ (2 - β - (d : ℝ))) * nf := by
          refine mul_le_mul_of_nonneg_right ?_ hnf
          exact mul_le_mul_of_nonneg_left hbound hfac
      _ = decayConst d Cp ω * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ)) * nf := by
          field_simp
  calc nG ≤ M * nf := hd'
    _ = (M * nf / (Xρ * s2)) * (Xρ * s2) := by field_simp
    _ ≤ (decayConst d Cp ω * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ)) * nf) * (Xρ * s2) :=
        mul_le_mul_of_nonneg_right hMnf hden.le

end PDE.Ch4GreenDecay
