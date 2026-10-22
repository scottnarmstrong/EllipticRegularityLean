module

public import EllipticRegularity.Ch4.Meyers.Sharpness

/-!
# The exponent `α(d, Λ)` of Meyers' example
-/

@[expose] public section

namespace PDE.Ch4Meyers

open MeasureTheory Set

/-- The exponent `α(d, Λ) = ½(-(d-2) + √((d-2)² + 4(d-1)/Λ))`. -/
noncomputable def examα (d : ℕ) (Λ : ℝ) : ℝ :=
  (1 / 2) * (-((d : ℝ) - 2) + Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ))

section
variable {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
include hd hΛ

theorem examα_sqrt_sq :
    Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ) ^ 2 =
      ((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ := by
  apply Real.sq_sqrt
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 ≤ 4 * ((d : ℝ) - 1) / Λ := div_nonneg (by linarith) (by linarith)
  positivity

theorem examα_pos : 0 < examα d Λ := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ0 : 0 < Λ := by linarith
  unfold examα
  have h1 : ((d : ℝ) - 2) < Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ) := by
    apply Real.lt_sqrt_of_sq_lt
    have : 0 < 4 * ((d : ℝ) - 1) / Λ := div_pos (by linarith) hΛ0
    linarith
  linarith

theorem examα_le_one : examα d Λ ≤ 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ0 : 0 < Λ := by linarith
  unfold examα
  have h1 : Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ) ≤ d := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith, ?_⟩
    have : 4 * ((d : ℝ) - 1) / Λ ≤ 4 * ((d : ℝ) - 1) := by
      rw [div_le_iff₀ hΛ0]; nlinarith
    nlinarith
  linarith

theorem examα_quadratic :
    examα d Λ ^ 2 + ((d : ℝ) - 2) * examα d Λ = ((d : ℝ) - 1) / Λ := by
  have hΛ0 : 0 < Λ := by linarith
  have h := examα_sqrt_sq hd hΛ
  unfold examα
  set s := Real.sqrt (((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) / Λ)
  have : ((d : ℝ) - 1) / Λ = (4 * ((d : ℝ) - 1) / Λ) / 4 := by ring
  rw [this]
  nlinarith [h]

theorem examα_eq_one_iff : examα d Λ = 1 ↔ Λ = 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ0 : 0 < Λ := by linarith
  have hq := examα_quadratic hd hΛ
  constructor
  · intro h
    rw [h] at hq
    have : ((d : ℝ) - 1) / Λ = (d : ℝ) - 1 := by linarith
    rw [div_eq_iff hΛ0.ne'] at this
    have h1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    nlinarith
  · intro h
    subst h
    have hq' : examα d 1 ^ 2 + ((d : ℝ) - 2) * examα d 1 = (d : ℝ) - 1 := by
      simpa using hq
    have hpos := examα_pos hd hΛ
    have hle := examα_le_one hd hΛ
    nlinarith

theorem examα_two (hd2 : d = 2) : examα d Λ = Λ ^ (-(1 / 2 : ℝ)) := by
  subst hd2
  unfold examα
  have hΛ0 : 0 < Λ := by linarith
  simp only [Nat.cast_ofNat, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add, neg_zero]
  rw [Real.rpow_neg hΛ0.le, ← Real.sqrt_eq_rpow]
  have : 4 * ((2 : ℝ) - 1) / Λ = 2 ^ 2 * Λ⁻¹ := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_inv]
  ring

end

end PDE.Ch4Meyers
