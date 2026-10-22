module

public import PDEFoundation.Analysis.RadialAverage

/-!
# Exact quadratic decay for dimension-weighted radial averages

This file isolates the constant-preserving radial calculation used in the
zero-center harmonic growth estimate.  Once a spherical square profile has
the form `r ^ 2 * G r` with `G` nondecreasing, its normalized ball profile
decays with the exact factor `(a / b) ^ 2`.

The harmonic route uses monotonicity of normalized gradient energy together
with the exact Green identity relating the radial derivative of the spherical
square average to that energy.  The one-dimensional consequences of those
facts are proved here without spending a constant.
-/

@[expose] public section

namespace PDE.Internal

open MeasureTheory Set

variable {d : ℕ}

/-- A quadratic radial factor raises the effective dimension by two.  Thus
monotonicity of the residual profile gives exact quadratic decay of the
dimension-`d` normalized radial integral. -/
theorem normalizedRadialIntegral_quadratic_decay [NeZero d]
    {G : ℝ → ℝ} (hG : Continuous G)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hGmono : MonotoneOn G (Ioc 0 b)) :
    (d : ℝ) / a ^ d * ∫ t in (0 : ℝ)..a, t ^ (d - 1) * (t ^ 2 * G t) ≤
      (a / b) ^ 2 *
        ((d : ℝ) / b ^ d * ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t)) := by
  let D : ℕ := d + 2
  let : NeZero D := ⟨by omega⟩
  have hmono := PDE.normalized_radialIntegral_mono (d := D) hG ha hab hGmono
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  have hDa :
      ∫ t in (0 : ℝ)..a, t ^ (D - 1) * G t =
        ∫ t in (0 : ℝ)..a, t ^ (d - 1) * (t ^ 2 * G t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [D]
    change t ^ (d + 1) * G t = t ^ (d - 1) * (t ^ 2 * G t)
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos
      (Nat.pos_of_ne_zero (NeZero.ne d))).symm⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hDb :
      ∫ t in (0 : ℝ)..b, t ^ (D - 1) * G t =
        ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [D]
    change t ^ (d + 1) * G t = t ^ (d - 1) * (t ^ 2 * G t)
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos
      (Nat.pos_of_ne_zero (NeZero.ne d))).symm⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hDa, hDb] at hmono
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hscale : 0 < (d : ℝ) / D := div_pos hdpos hDpos
  have hscaled := mul_le_mul_of_nonneg_left hmono hscale.le
  dsimp only [D] at hscaled
  push_cast at hscaled
  have hcore :
      ∫ t in (0 : ℝ)..a, t ^ (d - 1) * (t ^ 2 * G t) ≤
        a ^ (d + 2) / b ^ (d + 2) *
          ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t) := by
    field_simp [ha0, hb0, hd0] at hscaled ⊢
    simpa only [mul_assoc] using hscaled
  calc
    (d : ℝ) / a ^ d * ∫ t in (0 : ℝ)..a, t ^ (d - 1) * (t ^ 2 * G t) ≤
        (d : ℝ) / a ^ d * (a ^ (d + 2) / b ^ (d + 2) *
          ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t)) :=
      mul_le_mul_of_nonneg_left hcore (div_nonneg hdpos.le (pow_nonneg ha.le d))
    _ = (a / b) ^ 2 *
        ((d : ℝ) / b ^ d * ∫ t in (0 : ℝ)..b, t ^ (d - 1) * (t ^ 2 * G t)) := by
      rw [pow_add, pow_add]
      field_simp [ha0, hb0]

/-- The exact calculus step behind quadratic spherical growth.  If `H(0) = 0`
and `H'(r) = (2r / d) A(r)`, where the ball-energy profile `A` is
nondecreasing, then `H(r) / r²` is nondecreasing.  The proof integrates the
derivative and applies normalized radial monotonicity in dimension two.

For harmonic functions, `H` is the spherical average of the square and `A`
is the normalized ball average of the squared gradient.  Establishing their
displayed derivative relation is the separate Green/divergence identity. -/
theorem sphereProfile_div_sq_mono_of_hasDerivAt_energy [NeZero d]
    {H A : ℝ → ℝ} (hH0 : H 0 = 0) (hH : Continuous H) (hA : Continuous A)
    {R : ℝ} (hHderiv : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt H ((2 * r / d) * A r) r)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)
    (hAmono : MonotoneOn A (Ioc 0 b)) :
    H a / a ^ 2 ≤ H b / b ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hcont : ContinuousOn H (Icc 0 b) := hH.continuousOn
  have hprimitive : ∀ c : ℝ, 0 < c → c ≤ b →
      H c = (2 / d) * ∫ t in (0 : ℝ)..c, t * A t := by
    intro c hc hcb
    have hderiv : ∀ r ∈ Ioo (0 : ℝ) c,
        HasDerivAt H ((2 / d) * (r * A r)) r := by
      intro r hr
      convert hHderiv r ⟨hr.1, (hr.2.trans_le hcb).trans hbR⟩ using 1; ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := H) (f' := fun r => (2 / d) * (r * A r)) (a := 0) (b := c)
      hc.le (hcont.mono (Icc_subset_Icc_right hcb)) hderiv
      ((continuous_const.mul (continuous_id.mul hA)).intervalIntegrable 0 c)
    change (∫ y in (0 : ℝ)..c, (2 / d) * (y * A y)) = H c - H 0 at hint
    rw [hH0, sub_zero, intervalIntegral.integral_const_mul] at hint
    exact hint.symm
  have hradial := PDE.normalized_radialIntegral_mono (d := 2) hA ha hab hAmono
  rw [hprimitive a ha hab, hprimitive b hb le_rfl]
  norm_num at hradial ⊢
  have hdn : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (by exact_mod_cast Nat.zero_le d)
  have hscaled := mul_le_mul_of_nonneg_left hradial hdn
  field_simp [ha0, hb0, hd0] at hscaled ⊢
  simpa only [mul_assoc] using hscaled

end PDE.Internal
