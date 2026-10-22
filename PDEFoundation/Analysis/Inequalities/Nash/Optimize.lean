module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# Optimizing the tile size in the Nash inequality

If `X ≤ c ℓ² S + ℓ⁻ᵈ B²` for every `ℓ > 0` then `X ≤ 2 c S^{d/(d+2)} B^{4/(d+2)}` (for `c ≥ 1`).
-/

@[expose] public section

namespace PDE.Nash

open Filter Topology

/-- Optimization of the tile size, polynomial form. -/
theorem pow_le_of_forall_le {d : ℕ} (hd : 1 ≤ d) {c X S B : ℝ} (hc : 0 < c)
    (hX : 0 ≤ X) (hS : 0 < S) (hB : 0 < B)
    (h : ∀ ℓ : ℝ, 0 < ℓ → X ≤ c * ℓ ^ 2 * S + (ℓ ^ d)⁻¹ * B ^ 2) :
    X ^ (d + 2) ≤ 2 ^ (d + 2) * c ^ d * S ^ d * B ^ 4 := by
  set ρ : ℝ := (B ^ 2 / (c * S)) ^ ((1 : ℝ) / (d + 2)) with hρ
  have hq : 0 < B ^ 2 / (c * S) := by positivity
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hq _
  have hρpow : ρ ^ (d + 2) = B ^ 2 / (c * S) := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    have : (1 : ℝ) / (d + 2) * ((d + 2 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  have hkey : (ρ ^ d)⁻¹ * B ^ 2 = c * ρ ^ 2 * S := by
    have h2 : B ^ 2 = ρ ^ (d + 2) * (c * S) := by rw [hρpow]; field_simp
    rw [h2, pow_add]
    have : ρ ^ d ≠ 0 := (pow_pos hρpos d).ne'
    field_simp
  have h1 := h ρ hρpos
  rw [hkey] at h1
  have hX2 : X ≤ 2 * c * S * ρ ^ 2 := by linarith
  have h3 : X ^ (d + 2) ≤ (2 * c * S * ρ ^ 2) ^ (d + 2) := pow_le_pow_left₀ hX hX2 _
  refine h3.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_comm 2 (d + 2), pow_mul, hρpow]
  have hcS : c * S ≠ 0 := by positivity
  rw [mul_pow, mul_pow, div_pow]
  field_simp
  ring

theorem rpow_pow_eq {S : ℝ} (hS : 0 ≤ S) (a : ℝ) (n : ℕ) :
    (S ^ a) ^ n = S ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS]

/-- Optimization of the tile size, final form. -/
theorem le_rpow_of_forall_le {d : ℕ} (hd : 1 ≤ d) {c X S B : ℝ} (hc : 1 ≤ c)
    (hX : 0 ≤ X) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (h : ∀ ℓ : ℝ, 0 < ℓ → X ≤ c * ℓ ^ 2 * S + (ℓ ^ d)⁻¹ * B ^ 2) :
    X ≤ 2 * c * S ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := by
  have hc0 : 0 < c := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hnn : 0 ≤ 2 * c * S ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) := by positivity
  rcases hS.eq_or_lt with hS0 | hSpos
  · -- S = 0: let ℓ → ∞
    subst hS0
    have hlim : Tendsto (fun ℓ : ℝ => c * ℓ ^ 2 * 0 + (ℓ ^ d)⁻¹ * B ^ 2) atTop (𝓝 0) := by
      have : Tendsto (fun ℓ : ℝ => (ℓ ^ d)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))
      simpa using this.mul_const (B ^ 2)
    have := ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun ℓ hℓ => h ℓ (by linarith)⟩)
    exact this.trans hnn
  rcases hB.eq_or_lt with hB0 | hBpos
  · subst hB0
    have hlim : Tendsto (fun ℓ : ℝ => c * ℓ ^ 2 * S) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun ℓ : ℝ => c * ℓ ^ 2 * S) := by fun_prop
      have h0 := this.tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ℓ hℓ => by
      have := h ℓ hℓ; simpa using this)
    exact this.trans hnn
  have hpoly := pow_le_of_forall_le hd hc0 hX hSpos hBpos h
  have hpos1 : 0 < S ^ ((d : ℝ) / (d + 2)) := Real.rpow_pos_of_pos hSpos _
  have hpos2 : 0 < B ^ ((4 : ℝ) / (d + 2)) := Real.rpow_pos_of_pos hBpos _
  have hS' : (S ^ ((d : ℝ) / (d + 2))) ^ (d + 2) = S ^ d := by
    rw [rpow_pow_eq hSpos.le]
    have : (d : ℝ) / (d + 2) * ((d + 2 : ℕ) : ℝ) = (d : ℕ) := by push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have hB' : (B ^ ((4 : ℝ) / (d + 2))) ^ (d + 2) = B ^ 4 := by
    rw [rpow_pow_eq hBpos.le]
    have : (4 : ℝ) / (d + 2) * ((d + 2 : ℕ) : ℝ) = (4 : ℕ) := by push_cast; field_simp
    rw [this, Real.rpow_natCast]
  refine le_of_pow_le_pow_left₀ (n := d + 2) (by omega) hnn ?_
  rw [mul_pow, mul_pow, hS', hB']
  refine hpoly.trans ?_
  have : c ^ d ≤ c ^ (d + 2) := pow_le_pow_right₀ hc (by omega)
  have h4 : 0 ≤ S ^ d * B ^ 4 := by positivity
  calc 2 ^ (d + 2) * c ^ d * S ^ d * B ^ 4 = 2 ^ (d + 2) * c ^ d * (S ^ d * B ^ 4) := by ring
    _ ≤ 2 ^ (d + 2) * c ^ (d + 2) * (S ^ d * B ^ 4) := by gcongr
    _ = _ := by ring

end PDE.Nash
