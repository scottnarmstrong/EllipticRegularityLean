module

public import EllipticRegularity.DeGiorgi.Assembly.Statements

/-!
# Real exponent bookkeeping for the weak Harnack assembly
-/

@[expose] public section

namespace PDE.DGNMAssembly

/-- `Λ * (c Λ^{-1/2})^2 = c^2` for `Λ > 0`. -/
theorem mul_sq_rpow_neg_half {Λ c : ℝ} (hΛ : 0 < Λ) :
    Λ * (c * Λ ^ (-(1 : ℝ) / 2)) ^ 2 = c ^ 2 := by
  have h : (Λ ^ (-(1 : ℝ) / 2)) ^ 2 = Λ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ.le]
    norm_num [Real.rpow_neg_one]
  rw [mul_pow, h]
  field_simp

theorem rpow_neg_half_eq_inv_sqrt {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    Λ ^ (-(1 : ℝ) / 2) = (Real.sqrt Λ)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hΛ]
  congr 1
  ring

/-- The final exponent step: from `x ≤ Cs t^{-(d+2)}` power `1/g`. -/
theorem final_exponent_bound {Cs c Λ t e : ℝ} (hCs : 0 < Cs) (hc : 0 < c) (hΛ : 1 ≤ Λ)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (Cs * t ^ (-e)) ^ (1 / (c * Λ ^ (-(1 : ℝ) / 2))) ≤
      ((max 1 (max (Cs ^ (1 / c)) (e / c))) / t ^ (max 1 (max (Cs ^ (1 / c)) (e / c)))) ^
        Real.sqrt Λ := by
  set Cf := max 1 (max (Cs ^ (1 / c)) (e / c)) with hCf
  have hΛ0 : 0 ≤ Λ := by linarith
  have hs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have hsp : 0 < Real.sqrt Λ := Real.sqrt_pos.2 (by linarith)
  have hexp : 1 / (c * Λ ^ (-(1 : ℝ) / 2)) = (1 / c) * Real.sqrt Λ := by
    rw [rpow_neg_half_eq_inv_sqrt hΛ0]
    field_simp
  have hCf1 : 1 ≤ Cf := le_max_left _ _
  have hCf2 : Cs ^ (1 / c) ≤ Cf := (le_max_left _ _).trans (le_max_right _ _)
  have hCf3 : e / c ≤ Cf := (le_max_right _ _).trans (le_max_right _ _)
  have hpos : 0 < Cf := lt_of_lt_of_le one_pos hCf1
  rw [hexp, Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hs
  rw [Real.mul_rpow hCs.le (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le]
  have h1 : t ^ (-e * (1 / c)) ≤ t ^ (-Cf) := by
    apply Real.rpow_le_rpow_of_exponent_ge ht0 ht1
    have : e * (1 / c) ≤ Cf := by rw [mul_one_div]; exact hCf3
    linarith
  calc Cs ^ (1 / c) * t ^ (-e * (1 / c)) ≤ Cf * t ^ (-Cf) := by
        apply mul_le_mul hCf2 h1 (by positivity) hpos.le
    _ = Cf / t ^ Cf := by rw [Real.rpow_neg ht0.le, div_eq_mul_inv]

end PDE.DGNMAssembly
