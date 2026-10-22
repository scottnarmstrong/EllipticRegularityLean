/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.EnergyProfile
public import EllipticRegularity.Parabolic.Chain.Super.SliceForm

/-! # The window inequality for the power test

For a smooth cutoff `η` (with the gradient/time bounds of `PowCutoff`) and `v = u + ε`, the slice
form of the renormalized supersolution inequality for `F(s) = (s+ε)^r/r` and `φ = η²` gives, for
almost every pair of times `s < t`,
`F-pairing(s) - F-pairing(t) + ((1-r)/2) ∬_{U×(s,t]} η² v^(r-2) |∇u|² ≤ c₁ ∬_{Q ∩ U×(s,t]} v^r`.
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open MeasureTheory Set PDE PDE.Parabolic.Chain

variable {d : ℕ}

/-- Hypotheses on a space-time cutoff `η` supported in the set `Q`: smooth, between `0` and `1`,
laterally compactly supported in `U`, with `|∇η|² ≤ X` and `|η ∂ₜη| ≤ T` on `Q`. -/
structure PowCutoff (U : Set (Vec d)) (Q : Set (Vec d × ℝ)) (η : Vec d × ℝ → ℝ) (X T : ℝ) :
    Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  nonneg : ∀ z, 0 ≤ η z
  le_one : ∀ z, η z ≤ 1
  compact : ∃ Kx : Set (Vec d), IsCompact Kx ∧ Kx ⊆ U ∧ ∀ x t, x ∉ Kx → η (x, t) = 0
  grad : ∀ z, vecNormSq (parSpaceGrad η z) ≤ X * Q.indicator (fun _ => (1 : ℝ)) z
  time : ∀ z, |η z * parTimeDeriv η z| ≤ T * Q.indicator (fun _ => (1 : ℝ)) z
  hX : 0 ≤ X
  hT : 0 ≤ T

/-- `∇u` has integrable squared norm. -/
theorem parH1_integrable_vecNormSq_grad {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I) :
    Integrable (fun z => vecNormSq (u.grad z)) (volume.restrict (U ×ˢ I)) := by
  simp_rw [vecNormSq_eq_sum_sq]
  exact integrable_finsetSum _ fun i _ => (u.gradMemL2 i).integrable_sq

/-- The weighted gradient term is integrable. -/
theorem integrable_gradTerm {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I) {η : Vec d × ℝ → ℝ}
    (hη : Continuous η) (hη1 : ∀ z, η z ≤ 1) (hη0 : ∀ z, 0 ≤ η z) {r ε : ℝ} (hr : r < 1) (hε : 0 < ε)
    (hu0 : ∀ᵐ z ∂(volume.restrict (U ×ˢ I)), 0 ≤ u.toFun z) :
    Integrable (fun z => η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z))
      (volume.restrict (U ×ˢ I)) := by
  have hg := parH1_integrable_vecNormSq_grad u
  refine (hg.const_mul (ε ^ (r - 2))).mono' ?_ ?_
  · have h1 : AEMeasurable u.toFun (volume.restrict (U ×ˢ I)) :=
      u.memL2.aestronglyMeasurable.aemeasurable
    exact (((hη.measurable.pow_const 2).aemeasurable.mul
      ((h1.add_const ε).pow_const (r - 2))).mul hg.aemeasurable).aestronglyMeasurable
  · filter_upwards [hu0] with z hz
    have hN := vecNormSq_nonneg (u.grad z)
    have hv : ε ≤ u.toFun z + ε := by linarith
    have h2 : (u.toFun z + ε) ^ (r - 2) ≤ ε ^ (r - 2) :=
      Real.rpow_le_rpow_of_nonpos hε hv (by linarith)
    have h3 : 0 ≤ (u.toFun z + ε) ^ (r - 2) := (Real.rpow_pos_of_pos (by linarith) _).le
    have h4 : η z ^ 2 ≤ 1 := by nlinarith [hη0 z, hη1 z]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)
        ≤ 1 * ε ^ (r - 2) * vecNormSq (u.grad z) := by gcongr
      _ = _ := by ring


/-- Pointwise form of the window bound. -/
theorem ren_window_pointwise {U : Set (Vec d)} {I : Set ℝ} {Λ : ℝ} (a : ParCoeffField d)
    (u : ParH1Function U I) {F : ℝ → ℝ} {Q : Set (Vec d × ℝ)} {η : Vec d × ℝ → ℝ} {X T : ℝ}
    (hc : PowCutoff U Q η X T) {r ε : ℝ} (hr : r < 1) (hr0 : r ≠ 0) (hε : 0 < ε) {z : Vec d × ℝ}
    (hA : IsEllipticMatrix 1 Λ (a z)) (hu : 0 ≤ u.toFun z)
    (hF : F (u.toFun z) = (u.toFun z + ε) ^ r / r)
    (hF1 : deriv F (u.toFun z) = (u.toFun z + ε) ^ (r - 1))
    (hF2 : deriv (deriv F) (u.toFun z) = (r - 1) * (u.toFun z + ε) ^ (r - 2)) :
    renormalizedIntegrand a u F (fun w => η w ^ 2) z +
        ((1 - r) / 2) * (η z ^ 2 * (u.toFun z + ε) ^ (r - 2) * vecNormSq (u.grad z)) ≤
      (2 * T / |r| + 2 * Λ * X / (1 - r)) *
        Q.indicator (fun z => (u.toFun z + ε) ^ r) z := by
  have h := ren_power_le a u (hc.smooth.of_le (by simp)) hr hr0 hε hA hu hF hF1 hF2
  have hv : 0 ≤ (u.toFun z + ε) ^ r := (Real.rpow_pos_of_pos (by linarith) r).le
  have hΛ : 0 ≤ Λ := by have := hA.lam_le_Lam; have := hA.lam_pos; linarith
  have hr1 : 0 < 1 - r := by linarith
  have habs : 0 < |r| := abs_pos.2 hr0
  have e : ∀ c : ℝ, c * Q.indicator (fun z => (u.toFun z + ε) ^ r) z =
      c * (u.toFun z + ε) ^ r * Q.indicator (fun _ => (1 : ℝ)) z := by
    intro c
    by_cases hz : z ∈ Q <;> simp [hz]
  have h1 : (2 / |r|) * |η z * parTimeDeriv η z| * (u.toFun z + ε) ^ r ≤
      (2 * T / |r|) * (u.toFun z + ε) ^ r * Q.indicator (fun _ => (1 : ℝ)) z := by
    have := hc.time z
    have h2 : (2 / |r|) * |η z * parTimeDeriv η z| ≤
        (2 / |r|) * (T * Q.indicator (fun _ => (1 : ℝ)) z) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    calc _ ≤ (2 / |r|) * (T * Q.indicator (fun _ => (1 : ℝ)) z) * (u.toFun z + ε) ^ r :=
          mul_le_mul_of_nonneg_right h2 hv
      _ = _ := by ring
  have h3 : (2 / (1 - r)) * Λ * (u.toFun z + ε) ^ r * vecNormSq (parSpaceGrad η z) ≤
      (2 * Λ * X / (1 - r)) * (u.toFun z + ε) ^ r * Q.indicator (fun _ => (1 : ℝ)) z := by
    have := hc.grad z
    have h2 : (2 / (1 - r)) * Λ * (u.toFun z + ε) ^ r ≥ 0 := by positivity
    calc _ ≤ (2 / (1 - r)) * Λ * (u.toFun z + ε) ^ r *
          (X * Q.indicator (fun _ => (1 : ℝ)) z) := mul_le_mul_of_nonneg_left this h2
      _ = _ := by ring
  rw [add_mul, e, e]
  linarith [h, h1, h3]

end PDE.Parabolic.WeakHarnack
