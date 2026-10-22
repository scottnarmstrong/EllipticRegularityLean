/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-! # Global `C²` monotone profiles extending a function from `[ε, ∞)`

Given `f` with `f' = h`, `h' = k` on `(0, ∞)`, `h ≥ 0` and `k(ε) ≤ 0` on `[ε, ∞)`, we build a
global `C²` function `F` agreeing with `f` on `[ε, ∞)` (with matching first and second
derivatives), with `F' ≥ 0`, and with `F'`, `F''` bounded.  Below `ε` the second derivative is
`k(ε) e^{s-ε}`, so `F' = h(ε) + k(ε)(e^{s-ε} - 1) ∈ [h(ε), h(ε) - k(ε)]`.
This supplies the globally `C²` test profiles used in the parabolic weak Harnack inequality
(Proposition 5.13: powers `s^p`, `-s^(-p)`, `log s` of `v = u + ε ≥ ε`).
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open Set intervalIntegral

noncomputable section

/-- The second derivative of the profile: `k` on `[ε, ∞)`, `k(ε) e^{s-ε}` below. -/
def profG2 (ε : ℝ) (k : ℝ → ℝ) (s : ℝ) : ℝ := k (max s ε) * Real.exp (min (s - ε) 0)

/-- The first derivative of the profile. -/
def profF1 (ε : ℝ) (h k : ℝ → ℝ) (s : ℝ) : ℝ := h ε + ∫ r in ε..s, profG2 ε k r

/-- The profile. -/
def profF (ε : ℝ) (f h k : ℝ → ℝ) (s : ℝ) : ℝ := f ε + ∫ r in ε..s, profF1 ε h k r

variable {ε : ℝ} {f h k : ℝ → ℝ}

theorem profG2_continuous (hkc : ContinuousOn k (Ici ε)) : Continuous (profG2 ε k) := by
  unfold profG2
  have h1 : Continuous fun s => k (max s ε) :=
    hkc.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s ε
  exact h1.mul (Real.continuous_exp.comp (by fun_prop))

theorem profG2_of_le {s : ℝ} (hs : ε ≤ s) : profG2 ε k s = k s := by
  simp [profG2, max_eq_left hs, min_eq_right (sub_nonneg.2 hs)]

theorem profG2_of_ge {s : ℝ} (hs : s ≤ ε) : profG2 ε k s = k ε * Real.exp (s - ε) := by
  simp [profG2, max_eq_right hs, min_eq_left (sub_nonpos.2 hs)]

theorem profF1_hasDerivAt (hkc : ContinuousOn k (Ici ε)) (s : ℝ) :
    HasDerivAt (profF1 ε h k) (profG2 ε k s) s :=
  ((profG2_continuous hkc).integral_hasStrictDerivAt ε s).hasDerivAt.const_add _

theorem profF1_continuous (hkc : ContinuousOn k (Ici ε)) : Continuous (profF1 ε h k) :=
  continuous_iff_continuousAt.2 fun s => (profF1_hasDerivAt hkc s).continuousAt

theorem profF_hasDerivAt (hkc : ContinuousOn k (Ici ε)) (s : ℝ) :
    HasDerivAt (profF ε f h k) (profF1 ε h k s) s :=
  ((profF1_continuous hkc).integral_hasStrictDerivAt ε s).hasDerivAt.const_add _

theorem deriv_profF (hkc : ContinuousOn k (Ici ε)) : deriv (profF ε f h k) = profF1 ε h k :=
  funext fun s => (profF_hasDerivAt hkc s).deriv

theorem deriv_profF1 (hkc : ContinuousOn k (Ici ε)) : deriv (profF1 ε h k) = profG2 ε k :=
  funext fun s => (profF1_hasDerivAt hkc s).deriv

theorem profF_contDiff (hkc : ContinuousOn k (Ici ε)) : ContDiff ℝ 2 (profF ε f h k) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun s => (profF_hasDerivAt hkc s).differentiableAt, by simp, ?_⟩
  rw [deriv_profF hkc, contDiff_one_iff_deriv, deriv_profF1 hkc]
  exact ⟨fun s => (profF1_hasDerivAt hkc s).differentiableAt, profG2_continuous hkc⟩

/-- On `[ε, ∞)` the first derivative is `h`. -/
theorem profF1_of_le (hε : 0 < ε) (hh : ∀ s, 0 < s → HasDerivAt h (k s) s)
    (hkc : ContinuousOn k (Ici ε)) {s : ℝ} (hs : ε ≤ s) : profF1 ε h k s = h s := by
  unfold profF1
  have hcongr : ∫ r in ε..s, profG2 ε k r = ∫ r in ε..s, k r := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    exact profG2_of_le hr.1
  rw [hcongr, integral_eq_sub_of_hasDerivAt (f := h)]
  · ring
  · intro r hr
    rw [uIcc_of_le hs] at hr
    exact hh r (hε.trans_le hr.1)
  · refine (hkc.mono ?_).intervalIntegrable
    rw [uIcc_of_le hs]
    exact fun r hr => hr.1

/-- Below `ε` the first derivative is `h(ε) + k(ε)(e^{s-ε} - 1)`. -/
theorem profF1_of_ge {s : ℝ} (hs : s ≤ ε) :
    profF1 ε h k s = h ε + k ε * (Real.exp (s - ε) - 1) := by
  unfold profF1
  have hcongr : ∫ r in ε..s, profG2 ε k r = ∫ r in ε..s, k ε * Real.exp (r - ε) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_ge hs] at hr
    exact profG2_of_ge hr.2
  have hd : ∀ r ∈ uIcc ε s,
      HasDerivAt (fun r => k ε * Real.exp (r - ε)) (k ε * Real.exp (r - ε)) r := by
    intro r _
    have := (((hasDerivAt_id r).sub_const ε).exp).const_mul (k ε)
    simpa using this
  rw [hcongr, integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun r => k ε * Real.exp (r - ε)).intervalIntegrable _ _)]
  simp only [sub_self, Real.exp_zero]
  ring

/-- On `[ε, ∞)` the profile is `f`. -/
theorem profF_of_le (hε : 0 < ε) (hf : ∀ s, 0 < s → HasDerivAt f (h s) s)
    (hh : ∀ s, 0 < s → HasDerivAt h (k s) s)
    (hkc : ContinuousOn k (Ici ε)) {s : ℝ} (hs : ε ≤ s) : profF ε f h k s = f s := by
  unfold profF
  have hcongr : ∫ r in ε..s, profF1 ε h k r = ∫ r in ε..s, h r := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    exact profF1_of_le hε hh hkc hr.1
  rw [hcongr, integral_eq_sub_of_hasDerivAt (f := f)]
  · ring
  · intro r hr
    rw [uIcc_of_le hs] at hr
    exact hf r (hε.trans_le hr.1)
  · refine (ContinuousOn.intervalIntegrable ?_)
    intro r hr
    rw [uIcc_of_le hs] at hr
    exact (hh r (hε.trans_le hr.1)).continuousAt.continuousWithinAt

theorem profF1_nonneg (hε : 0 < ε) (hh : ∀ s, 0 < s → HasDerivAt h (k s) s)
    (hkc : ContinuousOn k (Ici ε)) (hh0 : ∀ s, ε ≤ s → 0 ≤ h s) (hk0 : k ε ≤ 0) (s : ℝ) :
    0 ≤ profF1 ε h k s := by
  rcases le_total ε s with hs | hs
  · rw [profF1_of_le hε hh hkc hs]
    exact hh0 s hs
  · rw [profF1_of_ge hs]
    have h1 : Real.exp (s - ε) - 1 ≤ 0 := by
      have := Real.exp_le_one_iff.2 (sub_nonpos.2 hs)
      linarith
    have := mul_nonneg_of_nonpos_of_nonpos hk0 h1
    have := hh0 ε le_rfl
    linarith

theorem abs_profF1_le (hε : 0 < ε) (hh : ∀ s, 0 < s → HasDerivAt h (k s) s)
    (hkc : ContinuousOn k (Ici ε)) (hh0 : ∀ s, ε ≤ s → 0 ≤ h s) (hk0 : k ε ≤ 0) {B : ℝ}
    (hhB : ∀ s, ε ≤ s → |h s| ≤ B) (hkB : ∀ s, ε ≤ s → |k s| ≤ B) (s : ℝ) :
    |profF1 ε h k s| ≤ 2 * B := by
  rw [abs_of_nonneg (profF1_nonneg hε hh hkc hh0 hk0 s)]
  rcases le_total ε s with hs | hs
  · rw [profF1_of_le hε hh hkc hs]
    have := (le_abs_self (h s)).trans (hhB s hs)
    have := (abs_nonneg (k ε)).trans (hkB ε le_rfl)
    linarith
  · rw [profF1_of_ge hs]
    have h1 : 0 ≤ Real.exp (s - ε) := (Real.exp_pos _).le
    have h2 : -k ε ≤ B := (neg_le_abs _).trans (hkB ε le_rfl)
    have h3 : Real.exp (s - ε) ≤ 1 := Real.exp_le_one_iff.2 (sub_nonpos.2 hs)
    have h4 : 0 ≤ -k ε := by linarith
    have h5 : -k ε * Real.exp (s - ε) ≤ -k ε := by nlinarith
    have := (le_abs_self (h ε)).trans (hhB ε le_rfl)
    nlinarith

theorem abs_profG2_le {B : ℝ} (hkB : ∀ s, ε ≤ s → |k s| ≤ B) (s : ℝ) : |profG2 ε k s| ≤ B := by
  unfold profG2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := hkB (max s ε) (le_max_right _ _)
  have h2 : Real.exp (min (s - ε) 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
  have h3 := abs_nonneg (k (max s ε))
  nlinarith [Real.exp_pos (min (s - ε) 0)]

/-- **Global `C²` monotone profile.**  Given `f' = h`, `h' = k` on `(0, ∞)`, `h ≥ 0` on `[ε, ∞)`,
`k` continuous on `[ε, ∞)` with `k(ε) ≤ 0`, and `|h|, |k| ≤ B` there, there is a globally `C²`
function `F`, Lipschitz, with `F' ≥ 0`, `|F'| ≤ 2B`, `|F''| ≤ B`, equal to `f` on `[ε, ∞)` with
`F' = h` and `F'' = k` there. -/
theorem exists_profile (hε : 0 < ε) (hf : ∀ s, 0 < s → HasDerivAt f (h s) s)
    (hh : ∀ s, 0 < s → HasDerivAt h (k s) s) (hkc : ContinuousOn k (Ici ε))
    (hh0 : ∀ s, ε ≤ s → 0 ≤ h s) (hk0 : k ε ≤ 0) {B : ℝ}
    (hhB : ∀ s, ε ≤ s → |h s| ≤ B) (hkB : ∀ s, ε ≤ s → |k s| ≤ B) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ (∀ s, 0 ≤ deriv F s) ∧ (∀ s, |deriv F s| ≤ 2 * B) ∧
      (∀ s, |deriv (deriv F) s| ≤ B) ∧ (∃ L : NNReal, LipschitzWith L F) ∧
      ∀ s, ε ≤ s → F s = f s ∧ deriv F s = h s ∧ deriv (deriv F) s = k s := by
  have hd1 := deriv_profF (f := f) (h := h) hkc
  have hd2 : deriv (deriv (profF ε f h k)) = profG2 ε k := by
    rw [hd1, deriv_profF1 hkc]
  have hC := profF_contDiff (f := f) (h := h) hkc
  refine ⟨profF ε f h k, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [hd1]
    exact profF1_nonneg hε hh hkc hh0 hk0 s
  · intro s
    rw [hd1]
    exact abs_profF1_le hε hh hkc hh0 hk0 hhB hkB s
  · intro s
    rw [hd2]
    exact abs_profG2_le hkB s
  · refine ⟨(2 * B).toNNReal, lipschitzWith_of_nnnorm_deriv_le
      (hC.differentiable (by norm_num)) fun s => ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    rw [Real.norm_eq_abs, hd1]
    exact (abs_profF1_le hε hh hkc hh0 hk0 hhB hkB s).trans (le_max_left _ _)
  · intro s hs
    refine ⟨profF_of_le hε hf hh hkc hs, ?_, ?_⟩
    · rw [hd1]
      exact profF1_of_le hε hh hkc hs
    · rw [hd2]
      exact profG2_of_le hs

end

end PDE.Parabolic.WeakHarnack
