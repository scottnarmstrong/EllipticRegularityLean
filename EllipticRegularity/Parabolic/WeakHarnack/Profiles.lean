/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.WeakHarnack.ProfilesCore
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Test profiles for the parabolic weak Harnack inequality

For `ε > 0` we produce globally `C²` Lipschitz functions `F` with `F' ≥ 0`, bounded `F'`, `F''`,
agreeing with `s^p` (`0 < p < 1`), `-s^(-p)` (`p > 0`), `log s` on `[ε, ∞)` together with their
first two derivatives.  Since `v = u + ε ≥ ε`, they are admissible in
`smooth_supersolution_renormalization` and recover the tests `η² v^(p-1)`, `η² v^(-p-1)`,
`ζ²/v` of the proof of Proposition 5.13 (manuscript, (5.19)).
-/

@[expose] public section

namespace PDE.Parabolic.WeakHarnack

open Set

/-- `F` is a globally `C²` monotone Lipschitz profile with bounded `F'`, `F''` extending
`f` (with `f' = h`, `f'' = k`) from `[ε, ∞)`. -/
def IsC2Profile (ε : ℝ) (F f h k : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧ (∀ s, 0 ≤ deriv F s) ∧ (∃ B, ∀ s, |deriv F s| ≤ B) ∧
    (∃ B, ∀ s, |deriv (deriv F) s| ≤ B) ∧ (∃ L : NNReal, LipschitzWith L F) ∧
    ∀ s, ε ≤ s → F s = f s ∧ deriv F s = h s ∧ deriv (deriv F) s = k s

/-- Generic existence of a profile (repackaging of `exists_profile`). -/
theorem exists_isC2Profile {ε : ℝ} {f h k : ℝ → ℝ} (hε : 0 < ε)
    (hf : ∀ s, 0 < s → HasDerivAt f (h s) s)
    (hh : ∀ s, 0 < s → HasDerivAt h (k s) s) (hkc : ContinuousOn k (Ici ε))
    (hh0 : ∀ s, ε ≤ s → 0 ≤ h s) (hk0 : k ε ≤ 0) {B : ℝ}
    (hhB : ∀ s, ε ≤ s → |h s| ≤ B) (hkB : ∀ s, ε ≤ s → |k s| ≤ B) :
    ∃ F, IsC2Profile ε F f h k := by
  obtain ⟨F, h1, h2, h3, h4, h5, h6⟩ := exists_profile hε hf hh hkc hh0 hk0 hhB hkB
  exact ⟨F, h1, h2, ⟨_, h3⟩, ⟨_, h4⟩, h5, h6⟩

/-- Profiles for the power functions `κ s^r`, `κ r ≥ 0`, `r ≤ 1`. -/
theorem exists_isC2Profile_power {ε κ r : ℝ} (hε : 0 < ε) (hκr : 0 ≤ κ * r) (hr : r ≤ 1) :
    ∃ F, IsC2Profile ε F (fun s => κ * s ^ r) (fun s => κ * r * s ^ (r - 1))
      (fun s => κ * r * (r - 1) * s ^ (r - 2)) := by
  have hderiv : ∀ (e c : ℝ) (s : ℝ), 0 < s →
      HasDerivAt (fun x : ℝ => c * x ^ e) (c * e * s ^ (e - 1)) s := by
    intro e c s hs
    have := (Real.hasDerivAt_rpow_const (x := s) (p := e) (Or.inl hs.ne')).const_mul c
    convert this using 1
    ring
  have hr1 : r - 1 ≤ 0 := by linarith
  have hr2 : r - 2 ≤ 0 := by linarith
  refine exists_isC2Profile (B := max (|κ * r| * ε ^ (r - 1)) (|κ * r * (r - 1)| * ε ^ (r - 2)))
    hε (fun s hs => hderiv r κ s hs) (fun s hs => ?_) ?_ ?_ ?_ ?_ ?_
  · have := hderiv (r - 1) (κ * r) s hs
    rw [show r - 1 - 1 = r - 2 by ring] at this
    exact this
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl hs0.ne'))).continuousWithinAt
  · intro s hs
    have : 0 ≤ s ^ (r - 1) := Real.rpow_nonneg (hε.le.trans hs) _
    positivity
  · have : κ * r * (r - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκr hr1
    have : 0 ≤ ε ^ (r - 2) := Real.rpow_nonneg hε.le _
    nlinarith
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hs hr1) (abs_nonneg _)).trans
      (le_max_left _ _)
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hs hr2) (abs_nonneg _)).trans
      (le_max_right _ _)

/-- **Profile (a)**: `F = s^p` on `[ε, ∞)`, `0 < p < 1`; the test is `η² F'(v) = p η² v^(p-1)`. -/
theorem exists_isC2Profile_pow {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1) :
    ∃ F, IsC2Profile ε F (fun s => s ^ p) (fun s => p * s ^ (p - 1))
      (fun s => p * (p - 1) * s ^ (p - 2)) := by
  obtain ⟨F, hF⟩ := exists_isC2Profile_power (κ := 1) (r := p) hε (by linarith) hp1.le
  simp only [one_mul] at hF
  exact ⟨F, hF⟩

/-- **Profile (b)**: `F = -s^(-p)` on `[ε, ∞)`, `p > 0`; `F' = p s^(-p-1)`. -/
theorem exists_isC2Profile_negpow {ε p : ℝ} (hε : 0 < ε) (hp : 0 < p) :
    ∃ F, IsC2Profile ε F (fun s => -s ^ (-p)) (fun s => p * s ^ (-p - 1))
      (fun s => -(p * (p + 1)) * s ^ (-p - 2)) := by
  obtain ⟨F, hF⟩ := exists_isC2Profile_power (κ := -1) (r := -p) hε (by nlinarith) (by linarith)
  have e1 : (fun s : ℝ => (-1 : ℝ) * s ^ (-p)) = fun s => -s ^ (-p) := by funext s; ring
  have e2 : (fun s : ℝ => (-1 : ℝ) * -p * s ^ (-p - 1)) = fun s => p * s ^ (-p - 1) := by
    funext s; ring
  have e3 : (fun s : ℝ => (-1 : ℝ) * -p * (-p - 1) * s ^ (-p - 2)) =
      fun s => -(p * (p + 1)) * s ^ (-p - 2) := by funext s; ring
  rw [e1, e2, e3] at hF
  exact ⟨F, hF⟩

/-- **Profile (c)**: `F = log s` on `[ε, ∞)`; `F' = 1/s`, `F'' = -1/s²`; the test is `ζ²/v`. -/
theorem exists_isC2Profile_log {ε : ℝ} (hε : 0 < ε) :
    ∃ F, IsC2Profile ε F Real.log (fun s => 1 / s) (fun s => -(1 / s ^ 2)) := by
  refine exists_isC2Profile (B := 1 / ε ^ 2 + 1 / ε) hε (fun s hs => ?_) (fun s hs => ?_)
    ?_ ?_ ?_ ?_ ?_
  · simpa only [one_div] using Real.hasDerivAt_log hs.ne'
  · have := hasDerivAt_inv hs.ne'
    simpa only [one_div, inv_pow] using this
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    exact ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hs0.ne')).neg).continuousWithinAt
  · intro s hs
    have := hε.trans_le hs
    positivity
  · have : 0 < 1 / ε ^ 2 := by positivity
    linarith
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    rw [abs_of_pos (by positivity)]
    have h1 : 1 / s ≤ 1 / ε := one_div_le_one_div_of_le hε hs
    have : 0 < 1 / ε ^ 2 := by positivity
    linarith
  · intro s hs
    have hs0 : 0 < s := hε.trans_le hs
    rw [abs_neg, abs_of_pos (by positivity)]
    have h1 : 1 / s ^ 2 ≤ 1 / ε ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε.le hs 2)
    have : 0 < 1 / ε := by positivity
    linarith

end PDE.Parabolic.WeakHarnack
