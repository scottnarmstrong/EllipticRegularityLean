module

public import PDEFoundation

/-!
# Constant bookkeeping for the Nash-Aronson lower bound

Pure real-number algebra, isolated from the PDE objects: the Harnack-chain loss `H^{-N}` with
`N ≤ 22 (1 + R² + D) + 1` dominates `c exp(-β D)` for the explicit constants used in the assembly.
-/

@[expose] public section

namespace PDE.Parabolic.NashLower

theorem exp_chain_loss_le {R H Dh : ℝ} (hH : 2 ≤ H) (N : ℕ)
    (hN : (N : ℝ) ≤ 22 * (1 + R ^ 2 + Dh) + 1) :
    Real.exp (-(22 * (1 + R ^ 2) + 1) * Real.log H) * Real.exp (-(22 * Real.log H) * Dh) ≤
      1 / H ^ N := by
  have hHpos : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hHN : H ^ N = Real.exp ((N : ℝ) * Real.log H) := by
    rw [Real.exp_nat_mul, Real.exp_log hHpos]
  rw [← Real.exp_add, hHN, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.2
  have h1 : (N : ℝ) * Real.log H ≤ (22 * (1 + R ^ 2 + Dh) + 1) * Real.log H :=
    mul_le_mul_of_nonneg_right hN hL
  nlinarith [h1]

theorem const_ineq {d : ℕ} {ω R₁ H h Dsq : ℝ} (hω : 0 < ω) (hR : 0 < R₁) (hH : 2 ≤ H)
    (hh : 0 < h) (N : ℕ) (hN : (N : ℝ) ≤ 22 * (1 + R₁ ^ 2 + Dsq / h) + 1) :
    (1 / (4 * ω * R₁ ^ d) * Real.exp (-(22 * (1 + R₁ ^ 2) + 1) * Real.log H)) *
        h ^ (-(d : ℝ) / 2) * Real.exp (-(22 * Real.log H) * Dsq / h) ≤
      1 / (4 * ((R₁ * Real.sqrt h) ^ d * ω)) / H ^ N := by
  have hsq : Real.sqrt h ^ d = h ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    congr 1; ring
  have e1 : (R₁ * Real.sqrt h) ^ d = R₁ ^ d * h ^ ((d : ℝ) / 2) := by rw [mul_pow, hsq]
  have e2 : h ^ (-(d : ℝ) / 2) = (h ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hh.le]; congr 1; ring
  have hexp := exp_chain_loss_le (R := R₁) (Dh := Dsq / h) hH N hN
  have e3 : -(22 * Real.log H) * Dsq / h = -(22 * Real.log H) * (Dsq / h) := by ring
  rw [e3, e1, e2]
  have hp : 0 < h ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hh _
  have hRd : 0 < R₁ ^ d := pow_pos hR d
  have hcoef : 1 / (4 * ((R₁ ^ d * h ^ ((d : ℝ) / 2)) * ω)) =
      1 / (4 * ω * R₁ ^ d) * (h ^ ((d : ℝ) / 2))⁻¹ := by
    field_simp
  rw [hcoef]
  have hpos : 0 ≤ 1 / (4 * ω * R₁ ^ d) * (h ^ ((d : ℝ) / 2))⁻¹ := by positivity
  calc 1 / (4 * ω * R₁ ^ d) * Real.exp (-(22 * (1 + R₁ ^ 2) + 1) * Real.log H) *
        (h ^ ((d : ℝ) / 2))⁻¹ * Real.exp (-(22 * Real.log H) * (Dsq / h))
      = (1 / (4 * ω * R₁ ^ d) * (h ^ ((d : ℝ) / 2))⁻¹) *
        (Real.exp (-(22 * (1 + R₁ ^ 2) + 1) * Real.log H) *
          Real.exp (-(22 * Real.log H) * (Dsq / h))) := by ring
    _ ≤ (1 / (4 * ω * R₁ ^ d) * (h ^ ((d : ℝ) / 2))⁻¹) * (1 / H ^ N) :=
        mul_le_mul_of_nonneg_left hexp hpos
    _ = _ := by rw [mul_one_div]

end PDE.Parabolic.NashLower
