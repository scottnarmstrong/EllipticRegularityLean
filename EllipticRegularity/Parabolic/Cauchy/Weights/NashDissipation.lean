module

public import PDEFoundation.Analysis.Inequalities.Nash.Main
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Nash inequality to scalar dissipation

The spatial Nash inequality is converted here into the nonlinear lower bound
on the Dirichlet energy used in the diagonal decay ODE. The constants are
kept explicit so the dependence on the initial `L¹` norm is visible.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Weights

/-- Rearranging Nash's inequality gives the gradient lower bound used in the
diagonal differential inequality. -/
theorem gradient_lower_of_nash {d : ℕ} (hd : 0 < d) {C E G B : ℝ}
    (hC : 0 < C) (hE : 0 < E) (hG : 0 ≤ G) (hB : 0 < B)
    (hNash : E ≤ C * G ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2))) :
    C ^ (-((d : ℝ) + 2) / d) * E ^ (1 + (2 : ℝ) / d) *
        B ^ (-(4 : ℝ) / d) ≤ G := by
  let q : ℝ := ((d : ℝ) + 2) / d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hGpos : 0 < G := by
    by_contra h
    have hGnonpos : G ≤ 0 := not_lt.mp h
    have hG0 : G = 0 := le_antisymm hGnonpos hG
    subst G
    have ha : 0 < (d : ℝ) / (d + 2) := by positivity
    have hzero : (0 : ℝ) ^ ((d : ℝ) / (d + 2)) = 0 :=
      Real.zero_rpow (ne_of_gt ha)
    rw [hzero] at hNash
    simp only [mul_zero, zero_mul] at hNash
    linarith
  have hGpow : 0 < G ^ ((d : ℝ) / (d + 2)) :=
    Real.rpow_pos_of_pos hGpos _
  have hBpow : 0 < B ^ ((4 : ℝ) / (d + 2)) :=
    Real.rpow_pos_of_pos hB _
  have hrightpos : 0 < C * G ^ ((d : ℝ) / (d + 2)) *
      B ^ ((4 : ℝ) / (d + 2)) := by positivity
  have hNashPow := Real.rpow_le_rpow hE.le hNash hq.le
  have hqG : ((d : ℝ) / (d + 2)) * q = 1 := by
    dsimp [q]
    field_simp
  have hqB : ((4 : ℝ) / (d + 2)) * q = (4 : ℝ) / d := by
    dsimp [q]
    field_simp
  have hfactor :
      (C * G ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2))) ^ q =
        C ^ q * G * B ^ ((4 : ℝ) / d) := by
    rw [show C * G ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)) =
      C * (G ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2))) by ring]
    rw [Real.mul_rpow hC.le (mul_nonneg (Real.rpow_nonneg hG _)
      (Real.rpow_nonneg hB.le _))]
    rw [Real.mul_rpow (Real.rpow_nonneg hG _) (Real.rpow_nonneg hB.le _)]
    rw [← Real.rpow_mul hG, ← Real.rpow_mul hB.le, hqG, Real.rpow_one, hqB]
    ring
  rw [hfactor] at hNashPow
  have hCinv : 0 ≤ C ^ (-q) := Real.rpow_nonneg hC.le _
  have hBinv : 0 ≤ B ^ (-(4 : ℝ) / d) := Real.rpow_nonneg hB.le _
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hNashPow hBinv) hCinv
  have hCcancel : C ^ (-q) * C ^ q = 1 := by
    rw [← Real.rpow_add hC, show -q + q = 0 by ring, Real.rpow_zero]
  have hBcancel : B ^ ((4 : ℝ) / d) * B ^ (-(4 : ℝ) / d) = 1 := by
    rw [← Real.rpow_add hB, show (4 : ℝ) / d + (-(4 : ℝ) / d) = 0 by ring,
      Real.rpow_zero]
  have hEexp : q = 1 + (2 : ℝ) / d := by
    dsimp [q]
    field_simp
  have hCexp : -((d : ℝ) + 2) / d = -q := by
    dsimp [q]
    ring
  calc
    _ = C ^ (-q) * (E ^ q * B ^ (-(4 : ℝ) / d)) := by
      rw [hCexp, hEexp]
      ring
    _ ≤ C ^ (-q) * ((C ^ q * G * B ^ ((4 : ℝ) / d)) *
          B ^ (-(4 : ℝ) / d)) := by
        exact hscaled
    _ = G := by
      rw [mul_assoc, hBcancel, mul_one, ← mul_assoc, hCcancel, one_mul]

/-- Energy dissipation plus Nash's inequality gives the scalar differential
inequality used by `nashDiagonalDecay_of_deriv`. -/
theorem nash_energy_derivative_bound {d : ℕ} (hd : 0 < d) {C E D B ED : ℝ}
    (hC : 0 < C) (hB : 0 < B) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hNash : E ≤ C * D ^ ((d : ℝ) / (d + 2)) * B ^ ((4 : ℝ) / (d + 2)))
    (hED : ED ≤ -2 * D) :
    ED ≤ -2 * (C ^ (-((d : ℝ) + 2) / d) * E ^ (1 + (2 : ℝ) / d) *
      B ^ (-(4 : ℝ) / d)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  by_cases hEpos : E = 0
  · have hpow : (0 : ℝ) ^ (1 + (2 : ℝ) / d) = 0 := by
      apply Real.zero_rpow
      have : 0 < (1 : ℝ) + (2 : ℝ) / d := by positivity
      exact ne_of_gt this
    have hED0 : ED ≤ 0 := by nlinarith
    rw [hEpos, hpow]
    simp only [mul_zero, zero_mul]
    exact hED0
  · have hEpos' : 0 < E := lt_of_le_of_ne hE (Ne.symm hEpos)
    have hgrad := gradient_lower_of_nash hd hC hEpos' hD hB hNash
    have hscaled : -2 * D ≤ -2 *
        (C ^ (-((d : ℝ) + 2) / d) * E ^ (1 + (2 : ℝ) / d) *
          B ^ (-(4 : ℝ) / d)) :=
      mul_le_mul_of_nonpos_left hgrad (by norm_num)
    exact hED.trans hscaled

end PDE.Parabolic.Cauchy.Weights
