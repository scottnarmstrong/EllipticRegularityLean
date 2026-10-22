module

public import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedDistance
public import PDEFoundation.Sobolev.W1p.Truncation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# A smooth positive extension of the shifted time variable

The weight `exp(q / (4 A (t-s+σ)))` is only used for `t ≥ s`, but the
whole-space weighted-energy API asks for a globally `C¹` multiplier. This
module extends the positive time variable smoothly to all real times, keeping
it equal to `t-s+σ` on the energy interval and uniformly bounded away from
zero.
-/

@[expose] public section

open Filter Topology

namespace PDE.Parabolic.Cauchy.Weights

/-- Smoothly extend `t + σ` from the half-line `t ≥ 0`, while staying positive
on the whole real line. -/
noncomputable def nashPositiveTimeShift (σ : ℝ) (t : ℝ) : ℝ :=
  σ + PDE.smoothPositivePartApprox (-σ / 4) (σ / 8) t -
    PDE.smoothPositivePartApprox (-σ / 4) (σ / 8) 0

theorem nashPositiveTimeShift_contDiff_one {σ : ℝ} :
    ContDiff ℝ 1 (nashPositiveTimeShift σ) := by
  have hF := PDE.smoothPositivePartApprox_contDiff_one (-σ / 4) (σ / 8)
  change ContDiff ℝ 1 (fun t => σ +
    PDE.smoothPositivePartApprox (-σ / 4) (σ / 8) t -
      PDE.smoothPositivePartApprox (-σ / 4) (σ / 8) 0)
  exact (contDiff_const.add hF).sub contDiff_const

theorem nashPositiveTimeShift_hasDerivAt {σ t : ℝ} :
    HasDerivAt (nashPositiveTimeShift σ)
      (PDE.smoothPositivePartStep (-σ / 4) (σ / 8) t) t := by
  let F : ℝ → ℝ := PDE.smoothPositivePartApprox (-σ / 4) (σ / 8)
  have h1 : HasDerivAt (fun z => σ + F z)
      (PDE.smoothPositivePartStep (-σ / 4) (σ / 8) t) t := by
    simpa [F] using
      (PDE.smoothPositivePartApprox_hasDerivAt (-σ / 4) (σ / 8) t).const_add σ
  have h2 : HasDerivAt (fun z => σ + F z - F 0)
      (PDE.smoothPositivePartStep (-σ / 4) (σ / 8) t) t := h1.sub_const (F 0)
  change HasDerivAt (fun z => σ + F z - F 0)
    (PDE.smoothPositivePartStep (-σ / 4) (σ / 8) t) t
  exact h2

theorem deriv_nashPositiveTimeShift {σ : ℝ} :
    deriv (nashPositiveTimeShift σ) =
      PDE.smoothPositivePartStep (-σ / 4) (σ / 8) := by
  funext t
  exact (nashPositiveTimeShift_hasDerivAt).deriv

theorem nashPositiveTimeShift_deriv_abs_le_one {σ t : ℝ} :
    |deriv (nashPositiveTimeShift σ) t| ≤ 1 := by
  rw [deriv_nashPositiveTimeShift]
  exact PDE.abs_smoothPositivePartStep_le_one (-σ / 4) (σ / 8) t

theorem nashPositiveTimeShift_deriv_nonneg {σ t : ℝ} :
    0 ≤ deriv (nashPositiveTimeShift σ) t := by
  rw [deriv_nashPositiveTimeShift]
  exact PDE.smoothPositivePartStep_nonneg (-σ / 4) (σ / 8) t

theorem nashPositiveTimeShift_deriv_le_one {σ t : ℝ} :
    deriv (nashPositiveTimeShift σ) t ≤ 1 := by
  rw [deriv_nashPositiveTimeShift]
  exact PDE.smoothPositivePartStep_le_one (-σ / 4) (σ / 8) t

theorem nashPositiveTimeShift_deriv_eq_one {σ t : ℝ} (hσ : 0 < σ)
    (ht : 0 ≤ t) : deriv (nashPositiveTimeShift σ) t = 1 := by
  rw [deriv_nashPositiveTimeShift]
  apply PDE.smoothPositivePartStep_eq_one
  · positivity
  · linarith

theorem nashPositiveTimeShift_lower {σ t : ℝ} (hσ : 0 < σ) :
    σ / 2 ≤ nashPositiveTimeShift σ t := by
  have hδ : 0 < σ / 8 := by positivity
  have hFnonneg := PDE.smoothPositivePartApprox_nonneg
    (c := -σ / 4) (δ := σ / 8) hδ t
  have hF0err := PDE.abs_smoothPositivePartApprox_sub_le
    (c := -σ / 4) (δ := σ / 8) hδ (0 : ℝ)
  have hF0 : PDE.smoothPositivePartApprox (-σ / 4) (σ / 8) 0 ≤ σ / 2 := by
    have htarget : max (0 - (-σ / 4)) 0 = σ / 4 := by
      have hpos : 0 ≤ σ / 4 := by positivity
      have harg : 0 - (-σ) / 4 = σ / 4 := by ring
      rw [harg, max_eq_left hpos]
    rw [htarget] at hF0err
    have habs := abs_le.mp hF0err
    linarith
  dsimp [nashPositiveTimeShift]
  linarith

theorem nashPositiveTimeShift_eq_add {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    nashPositiveTimeShift σ t = t + σ := by
  let F : ℝ → ℝ := PDE.smoothPositivePartApprox (-σ / 4) (σ / 8)
  have hδ : 0 < σ / 8 := by positivity
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) t, HasDerivAt F 1 r := by
    intro r hr
    have hr0 : 0 ≤ r := by
      rw [Set.uIcc_of_le ht] at hr
      exact hr.1
    have hstep : PDE.smoothPositivePartStep (-σ / 4) (σ / 8) r = 1 := by
      apply PDE.smoothPositivePartStep_eq_one hδ
      linarith
    have h := PDE.smoothPositivePartApprox_hasDerivAt (-σ / 4) (σ / 8) r
    simpa [F, hstep] using h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) hderiv intervalIntegrable_const
  have hFdiff : F t - F 0 = t := by
    calc
      F t - F 0 = ∫ r in (0 : ℝ)..t, (1 : ℝ) := hFTC.symm
      _ = t := by simp [intervalIntegral.integral_const]
  dsimp [nashPositiveTimeShift, F]
  change σ + F t - F 0 = t + σ
  calc
    σ + F t - F 0 = σ + (F t - F 0) := by ring
    _ = σ + t := by rw [hFdiff]
    _ = t + σ := by ring

end PDE.Parabolic.Cauchy.Weights
