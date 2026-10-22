/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
-/
module

public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.Cutoff.Profile
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Smooth convex approximations to absolute value -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.L1

open Filter
open scoped Topology

/-- A smooth, convex approximation to absolute value, with value zero at zero. -/
noncomputable def cauchyAbsEntropy (δ : ℝ) (x : ℝ) : ℝ :=
  PDE.smoothPositivePartApprox 0 δ x + PDE.smoothPositivePartApprox 0 δ (-x)

theorem cauchyAbsEntropy_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cauchyAbsEntropy δ) := by
  unfold cauchyAbsEntropy
  exact (PDE.smoothPositivePartApprox_contDiff 0 δ).add
    ((PDE.smoothPositivePartApprox_contDiff 0 δ).comp contDiff_neg)

theorem cauchyAbsEntropy_zero (δ : ℝ) : cauchyAbsEntropy δ 0 = 0 := by
  simp [cauchyAbsEntropy, PDE.smoothPositivePartApprox]

theorem cauchyAbsEntropy_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ cauchyAbsEntropy δ x := by
  unfold cauchyAbsEntropy
  exact add_nonneg (PDE.smoothPositivePartApprox_nonneg hδ x)
    (PDE.smoothPositivePartApprox_nonneg hδ (-x))

theorem cauchyAbsEntropy_le_abs {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    cauchyAbsEntropy δ x ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · have hzero := PDE.smoothPositivePartApprox_eq_zero_of_le hδ (by linarith : -x ≤ 0)
    rw [cauchyAbsEntropy, hzero, add_zero, abs_of_nonneg hx]
    have h := PDE.abs_smoothPositivePartApprox_le 0 δ x
    rw [abs_of_nonneg (PDE.smoothPositivePartApprox_nonneg hδ x), sub_zero,
      abs_of_nonneg hx] at h
    exact h
  · have hzero := PDE.smoothPositivePartApprox_eq_zero_of_le hδ hx
    rw [cauchyAbsEntropy, hzero, zero_add, abs_of_nonpos hx]
    have h := PDE.abs_smoothPositivePartApprox_le 0 δ (-x)
    rw [abs_of_nonneg (PDE.smoothPositivePartApprox_nonneg hδ (-x)), sub_zero,
      abs_of_nonneg (by linarith : 0 ≤ -x)] at h
    simpa using h

theorem cauchyAbsEntropy_abs_sub_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    abs (cauchyAbsEntropy δ x - abs x) ≤ 2 * δ := by
  rcases le_total 0 x with hx | hx
  · rw [cauchyAbsEntropy, PDE.smoothPositivePartApprox_eq_zero_of_le hδ
      (by linarith : -x ≤ 0), add_zero, abs_of_nonneg hx]
    simpa [max_eq_left hx, sub_zero] using
      (PDE.abs_smoothPositivePartApprox_sub_le (c := 0) hδ x)
  · rw [cauchyAbsEntropy, PDE.smoothPositivePartApprox_eq_zero_of_le hδ hx,
      zero_add, abs_of_nonpos hx]
    have h := PDE.abs_smoothPositivePartApprox_sub_le (c := 0) hδ (-x)
    simpa [max_eq_left (by linarith : 0 ≤ -x), sub_zero,
      abs_of_nonneg (by linarith : 0 ≤ -x)] using h

theorem cauchyAbsEntropy_tendsto_abs (x : ℝ) :
    Tendsto (fun n : ℕ => cauchyAbsEntropy (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 |x|) := by
  have hn : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hInv := tendsto_inv_atTop_zero.comp hcast
    convert hInv using 1
    · ext n
      simp [one_div]
  have hδ : ∀ n : ℕ, 0 < (1 : ℝ) / ((n : ℝ) + 1) := by intro n; positivity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => |x| - 2 * (1 / ((n : ℝ) + 1)))
    (h := fun n : ℕ => |x| + 2 * (1 / ((n : ℝ) + 1)))
  · exact (tendsto_const_nhds.sub (hn.const_mul 2)).trans (by simp)
  · exact (tendsto_const_nhds.add (hn.const_mul 2)).trans (by simp)
  · intro n
    have h := cauchyAbsEntropy_abs_sub_le (hδ n) x
    rw [abs_le] at h
    linarith
  · intro n
    have h := cauchyAbsEntropy_abs_sub_le (hδ n) x
    rw [abs_le] at h
    linarith

theorem cauchyAbsEntropy_deriv {δ : ℝ} (_hδ : 0 < δ) (x : ℝ) :
    deriv (cauchyAbsEntropy δ) x =
      PDE.smoothPositivePartStep 0 δ x - PDE.smoothPositivePartStep 0 δ (-x) := by
  have h₁ := PDE.smoothPositivePartApprox_hasDerivAt 0 δ x
  have h₂₀ := PDE.smoothPositivePartApprox_hasDerivAt 0 δ (-x)
  have h₂ := h₂₀.comp x (hasDerivAt_neg x)
  change deriv (fun y => PDE.smoothPositivePartApprox 0 δ y +
      PDE.smoothPositivePartApprox 0 δ (-y)) x = _
  calc
    _ = deriv (PDE.smoothPositivePartApprox 0 δ +
        PDE.smoothPositivePartApprox 0 δ ∘ Neg.neg) x := by rfl
    _ = PDE.smoothPositivePartStep 0 δ x +
        PDE.smoothPositivePartStep 0 δ (-x) * -1 := (h₁.add h₂).deriv
    _ = _ := by ring

private theorem smoothPositivePartStep_monotone {δ : ℝ} (hδ : 0 < δ) :
    Monotone (PDE.smoothPositivePartStep 0 δ) := by
  intro x y hxy
  unfold PDE.smoothPositivePartStep
  apply Real.smoothTransition.monotone
  have hdiv : (x - 0) / δ ≤ (y - 0) / δ := by
    exact div_le_div_of_nonneg_right (by simpa using hxy) hδ.le
  linarith only [hdiv]

private theorem deriv_smoothPositivePartStep_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ deriv (PDE.smoothPositivePartStep 0 δ) x :=
  (smoothPositivePartStep_monotone hδ).deriv_nonneg (x := x)

private theorem deriv_smoothPositivePartStep_abs_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (PDE.smoothPositivePartStep 0 δ) x| ≤ 8 / δ := by
  let q : ℝ → ℝ := fun y => y / δ - 1
  have hq : HasDerivAt q δ⁻¹ x := by
    have hid := (hasDerivAt_id x).div_const δ
    change HasDerivAt (fun y => y / δ - 1) δ⁻¹ x
    convert hid.sub_const 1 using 1 <;> simp [one_div]
  have hprof :=
    (PDE.smoothTransitionProfile.smooth.differentiable (by simp)
      ((x / δ) - 1)).hasDerivAt
  have hcomp := hprof.comp x hq
  have hfun : (fun y : ℝ => PDE.smoothPositivePartStep 0 δ y) =
      PDE.smoothTransitionProfile ∘ q := by
    funext y
    simp [q, PDE.smoothPositivePartStep, PDE.smoothTransitionProfile]
  have hderiv : deriv (PDE.smoothPositivePartStep 0 δ) x =
      deriv PDE.smoothTransitionProfile ((x / δ) - 1) * δ⁻¹ := by
    calc
      deriv (PDE.smoothPositivePartStep 0 δ) x =
          deriv (fun y => PDE.smoothPositivePartStep 0 δ y) x := rfl
      _ = deriv (PDE.smoothTransitionProfile ∘ q) x := by rw [hfun]
      _ = _ := by simpa [q] using hcomp.deriv
  rw [hderiv, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  calc
    |deriv PDE.smoothTransitionProfile ((x / δ) - 1)| * δ⁻¹ ≤
        8 * δ⁻¹ := by
          exact mul_le_mul_of_nonneg_right
            (PDE.smoothTransitionProfile.abs_deriv_le_eight _) (inv_nonneg.mpr hδ.le)
    _ = 8 / δ := by field_simp

theorem cauchyAbsEntropy_secondDeriv_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ deriv (deriv (cauchyAbsEntropy δ)) x := by
  have hstep : ContDiff ℝ (⊤ : ℕ∞) (PDE.smoothPositivePartStep 0 δ) :=
    PDE.smoothPositivePartStep_contDiff 0 δ
  have hstepD : Differentiable ℝ (PDE.smoothPositivePartStep 0 δ) :=
    hstep.differentiable (by norm_num)
  have h₂ : HasDerivAt (fun y : ℝ =>
      PDE.smoothPositivePartStep 0 δ y - PDE.smoothPositivePartStep 0 δ (-y))
      (deriv (PDE.smoothPositivePartStep 0 δ) x +
        deriv (PDE.smoothPositivePartStep 0 δ) (-x)) x := by
    have h₁ := (hstepD x).hasDerivAt
    have hneg := (hstepD (-x)).hasDerivAt.comp x (hasDerivAt_neg x)
    convert h₁.sub hneg using 1
    · funext y
      rfl
    · ring
  have hderivFun : deriv (cauchyAbsEntropy δ) =
      fun y => PDE.smoothPositivePartStep 0 δ y - PDE.smoothPositivePartStep 0 δ (-y) :=
    funext fun y => cauchyAbsEntropy_deriv hδ y
  have hEq : deriv (deriv (cauchyAbsEntropy δ)) x =
      deriv (PDE.smoothPositivePartStep 0 δ) x +
        deriv (PDE.smoothPositivePartStep 0 δ) (-x) := by
    rw [hderivFun]
    exact h₂.deriv
  rw [hEq]
  exact add_nonneg (deriv_smoothPositivePartStep_nonneg hδ x)
    (deriv_smoothPositivePartStep_nonneg hδ (-x))

theorem cauchyAbsEntropy_secondDeriv_abs_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (deriv (cauchyAbsEntropy δ)) x| ≤ 16 / δ := by
  have hderivFun : deriv (cauchyAbsEntropy δ) =
      fun y => PDE.smoothPositivePartStep 0 δ y - PDE.smoothPositivePartStep 0 δ (-y) :=
    funext fun y => cauchyAbsEntropy_deriv hδ y
  have h₂ : HasDerivAt (fun y : ℝ =>
      PDE.smoothPositivePartStep 0 δ y - PDE.smoothPositivePartStep 0 δ (-y))
      (deriv (PDE.smoothPositivePartStep 0 δ) x +
        deriv (PDE.smoothPositivePartStep 0 δ) (-x)) x := by
    have h₁ :=
      ((PDE.smoothPositivePartStep_contDiff 0 δ).differentiable (by norm_num) x).hasDerivAt
    have hneg :=
      ((PDE.smoothPositivePartStep_contDiff 0 δ).differentiable (by norm_num) (-x)).hasDerivAt
        |>.comp x (hasDerivAt_neg x)
    convert h₁.sub hneg using 1
    · funext y
      rfl
    · ring
  rw [hderivFun, h₂.deriv]
  calc
      |deriv (PDE.smoothPositivePartStep 0 δ) x +
        deriv (PDE.smoothPositivePartStep 0 δ) (-x)| ≤
      |deriv (PDE.smoothPositivePartStep 0 δ) x| +
        |deriv (PDE.smoothPositivePartStep 0 δ) (-x)| := abs_add_le _ _
    _ ≤ 8 / δ + 8 / δ := add_le_add
      (deriv_smoothPositivePartStep_abs_le hδ x)
      (deriv_smoothPositivePartStep_abs_le hδ (-x))
    _ = 16 / δ := by ring

theorem cauchyAbsEntropy_deriv_abs_le_one {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (cauchyAbsEntropy δ) x| ≤ 1 := by
  rw [cauchyAbsEntropy_deriv hδ x]
  rcases le_total 0 x with hx | hx
  · have hzero := PDE.smoothPositivePartStep_eq_zero hδ (by linarith : -x ≤ 0 + δ)
    rw [hzero, sub_zero]
    exact PDE.abs_smoothPositivePartStep_le_one 0 δ x
  · have hzero := PDE.smoothPositivePartStep_eq_zero hδ (by linarith : x ≤ 0 + δ)
    rw [hzero, zero_sub, abs_neg]
    exact PDE.abs_smoothPositivePartStep_le_one 0 δ (-x)

theorem cauchyAbsEntropy_lipschitz {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : NNReal, LipschitzWith C (cauchyAbsEntropy δ) := by
  let C : NNReal := 1
  have hdiff : Differentiable ℝ (cauchyAbsEntropy δ) :=
    (cauchyAbsEntropy_contDiff δ).differentiable (by norm_num)
  have hbound : ∀ x, ‖deriv (cauchyAbsEntropy δ) x‖₊ ≤ C := by
    intro x
    apply_mod_cast (cauchyAbsEntropy_deriv_abs_le_one hδ x)
  exact ⟨C, lipschitzWith_of_nnnorm_deriv_le hdiff hbound⟩

theorem cauchyAbsEntropy_deriv_abs_le_linear {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |deriv (cauchyAbsEntropy δ) x| ≤ (16 / δ) * |x| := by
  by_cases hx : 0 ≤ x
  · have hminus : PDE.smoothPositivePartStep 0 δ (-x) = 0 :=
      PDE.smoothPositivePartStep_eq_zero hδ (by linarith : -x ≤ 0 + δ)
    rw [cauchyAbsEntropy_deriv hδ x, hminus]
    by_cases hδx : x ≤ δ
    · have hzero' := PDE.smoothPositivePartStep_eq_zero hδ
        (by linarith : x ≤ 0 + δ)
      rw [hzero', sub_zero]
      simpa only [abs_zero] using
        (mul_nonneg (by positivity : 0 ≤ (16 : ℝ) / δ) (abs_nonneg x))
    · have hxδ : δ < x := lt_of_not_ge hδx
      rw [sub_zero, abs_of_nonneg (PDE.smoothPositivePartStep_nonneg 0 δ x)]
      rw [abs_of_nonneg hx]
      have hcoef : (1 : ℝ) ≤ (16 / δ) * x := by
        have hdiv : 1 ≤ x / δ := (le_div_iff₀ hδ).2 (by linarith)
        have heq : (16 / δ) * x = 16 * (x / δ) := by field_simp
        rw [heq]
        nlinarith
      exact (PDE.smoothPositivePartStep_le_one 0 δ x).trans (by linarith)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hplus : PDE.smoothPositivePartStep 0 δ x = 0 :=
      PDE.smoothPositivePartStep_eq_zero hδ (by linarith : x ≤ 0 + δ)
    rw [cauchyAbsEntropy_deriv hδ x, hplus, zero_sub, abs_neg]
    by_cases hδx : -x ≤ δ
    · have hzero' := PDE.smoothPositivePartStep_eq_zero hδ
        (by linarith : -x ≤ 0 + δ)
      rw [hzero']
      simpa only [abs_zero] using
        (mul_nonneg (by positivity : 0 ≤ (16 : ℝ) / δ) (abs_nonneg x))
    · have hxδ : δ < -x := lt_of_not_ge hδx
      rw [abs_of_nonneg (PDE.smoothPositivePartStep_nonneg 0 δ (-x)),
        abs_of_nonpos hx']
      have hcoef : (1 : ℝ) ≤ (16 / δ) * (-x) := by
        have hdiv : 1 ≤ (-x) / δ := (le_div_iff₀ hδ).2 (by linarith)
        have heq : (16 / δ) * (-x) = 16 * ((-x) / δ) := by field_simp
        rw [heq]
        nlinarith
      exact (PDE.smoothPositivePartStep_le_one 0 δ (-x)).trans (by linarith)

end PDE.Parabolic.Cauchy.L1
