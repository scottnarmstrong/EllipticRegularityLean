/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.Pointwise
public import EllipticRegularity.Parabolic.WeakHarnack.Profiles
public import EllipticRegularity.Parabolic.LocalMax.SliceSobolev

/-! # Pointwise energy bound for the unified power test `η² v^(r-1)`, `r < 1`, `r ≠ 0`

For the profile `F(s) = (s+ε)^r / r` (so `F(u) = v^r / r`, `F' = v^(r-1)`, `F'' = (r-1) v^(r-2)`
with `v = u + ε`) and the test function `φ = η²`, the renormalized integrand is bounded by
`(2/|r|) |η ∂ₜη| v^r + (2Λ/(1-r)) v^r |∇η|² - ((1-r)/2) η² v^(r-2) |∇u|²`.
Positive powers are `0 < r < 1`, negative powers are `r = -p < 0`.
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open PDE PDE.Parabolic.Chain

variable {d : ℕ}

/-- `parTimeDeriv` and `parSpaceGrad` of a square. -/
theorem parTimeDeriv_sq {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (z : Vec d × ℝ) :
    parTimeDeriv (fun w => η w ^ 2) z = 2 * η z * parTimeDeriv η z := by
  have := parTimeDeriv_mul hη hη z
  simp only [← sq] at this
  rw [this]; ring

theorem parSpaceGrad_sq {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ 1 η) (z : Vec d × ℝ) :
    parSpaceGrad (fun w => η w ^ 2) z = (2 * η z) • parSpaceGrad η z := by
  have := parSpaceGrad_mul hη hη z
  simp only [← sq] at this
  rw [this, ← two_smul ℝ, smul_smul]

/-- **Pointwise bound** for the renormalized integrand of the power profile. -/
theorem ren_power_le {U : Set (Vec d)} {I : Set ℝ} {Λ : ℝ} (a : ParCoeffField d)
    (u : ParH1Function U I) {F : ℝ → ℝ} {η : Vec d × ℝ → ℝ} (hη : ContDiff ℝ 1 η)
    {r ε : ℝ} (hr : r < 1) (hr0 : r ≠ 0) (hε : 0 < ε) {z : Vec d × ℝ}
    (hA : IsEllipticMatrix 1 Λ (a z)) (hu : 0 ≤ u.toFun z)
    (hF : F (u.toFun z) = (u.toFun z + ε) ^ r / r)
    (hF1 : deriv F (u.toFun z) = (u.toFun z + ε) ^ (r - 1))
    (hF2 : deriv (deriv F) (u.toFun z) = (r - 1) * (u.toFun z + ε) ^ (r - 2)) :
    renormalizedIntegrand a u F (fun w => η w ^ 2) z ≤
      (2 / |r|) * |η z * parTimeDeriv η z| * (u.toFun z + ε) ^ r +
        (2 / (1 - r)) * Λ * (u.toFun z + ε) ^ r * vecNormSq (parSpaceGrad η z) -
        ((1 - r) / 2) * (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) := by
  have hv : 0 < u.toFun z + ε := by linarith
  rw [renormalizedIntegrand_eq_time_add_gradPart, hF1, hF2, hF, parTimeDeriv_sq hη,
    parSpaceGrad_sq hη]
  have hg := gradPart_power_le hA (u.grad z) (parSpaceGrad η z) (κ := r⁻¹) (r := r) (η := η z)
    hv (by rw [inv_mul_cancel₀ hr0]; exact one_pos) hr
  simp only [inv_mul_cancel₀ hr0, one_mul] at hg
  have hg' : gradPart ((u.toFun z + ε) ^ (r - 1)) ((r - 1) * (u.toFun z + ε) ^ (r - 2)) (a z)
      (u.grad z) (η z ^ 2) ((2 * η z) • parSpaceGrad η z) ≤
      -((1 - r) / 2) * η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z) +
        2 * (1 / (1 - r)) * (u.toFun z + ε) ^ r * Λ * vecNormSq (parSpaceGrad η z) := hg
  have hvr : 0 ≤ (u.toFun z + ε) ^ r := (Real.rpow_pos_of_pos hv r).le
  have ht : -((u.toFun z + ε) ^ r / r * (2 * η z * parTimeDeriv η z)) ≤
      (2 / |r|) * |η z * parTimeDeriv η z| * (u.toFun z + ε) ^ r := by
    have h1 : -((u.toFun z + ε) ^ r / r * (2 * η z * parTimeDeriv η z)) =
        -((2 * (η z * parTimeDeriv η z)) / r) * (u.toFun z + ε) ^ r := by ring
    rw [h1]
    have h2 : -((2 * (η z * parTimeDeriv η z)) / r) ≤ (2 / |r|) * |η z * parTimeDeriv η z| := by
      have : |(2 * (η z * parTimeDeriv η z)) / r| = (2 / |r|) * |η z * parTimeDeriv η z| := by
        rw [abs_div, abs_mul, abs_two]; ring
      rw [← this]; exact neg_le_abs _
    exact mul_le_mul_of_nonneg_right h2 hvr
  refine (add_le_add ht hg').trans (le_of_eq ?_)
  ring

end PDE.Parabolic.WeakHarnack
