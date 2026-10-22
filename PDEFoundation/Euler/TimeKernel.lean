module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import PDEFoundation.Euler.Defs

/-!
# One-dimensional time mollifiers

`etaK n` is the normalised smooth bump on `ℝ` with outer radius `δ n = 1/(n+1)`: nonnegative, even, smooth,
mass one, supported in `[-δ n, δ n]`.  `thetaK n r = ∫_{r}^{δ n} etaK n` is its smooth cut-off primitive:
`thetaK n' = -etaK n`, `thetaK n r = 1` for `r ≤ -δ n`, `= 0` for `r ≥ δ n`, `thetaK n 0 = 1/2`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace PDE

/-- The time-scale `1/(n+1)`. -/
noncomputable def tDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tDelta_pos (n : ℕ) : 0 < tDelta n := by unfold tDelta; positivity

theorem tendsto_tDelta : Tendsto tDelta atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tDelta_le_one (n : ℕ) : tDelta n ≤ 1 := by
  unfold tDelta
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  exact (div_le_one (by positivity)).2 this

/-- The smooth bump on `ℝ` with radii `δ n / 2 < δ n`. -/
noncomputable def timeBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨tDelta n / 2, tDelta n, half_pos (tDelta_pos n), half_lt_self (tDelta_pos n)⟩

/-- Normalised time mollifier. -/
noncomputable def etaK (n : ℕ) : ℝ → ℝ := (timeBump n).normed volume

theorem etaK_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (etaK n) := (timeBump n).contDiff_normed

theorem etaK_nonneg (n : ℕ) (s : ℝ) : 0 ≤ etaK n s := (timeBump n).nonneg_normed s

theorem etaK_neg (n : ℕ) (s : ℝ) : etaK n (-s) = etaK n s := (timeBump n).normed_neg s

theorem etaK_integral (n : ℕ) : ∫ s, etaK n s = 1 := (timeBump n).integral_normed

theorem etaK_integrable (n : ℕ) : Integrable (etaK n) := (timeBump n).integrable_normed

theorem etaK_hasCompactSupport (n : ℕ) : HasCompactSupport (etaK n) :=
  (timeBump n).hasCompactSupport_normed

theorem etaK_eq_zero (n : ℕ) {s : ℝ} (hs : tDelta n ≤ |s|) : etaK n s = 0 := by
  have h : s ∉ Function.support (etaK n) := by
    rw [etaK, (timeBump n).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact not_lt.2 hs
  simpa using h

theorem etaK_le_const (n : ℕ) : ∃ C, ∀ s, |etaK n s| ≤ C := by
  obtain ⟨C, hC⟩ := (etaK_hasCompactSupport n).exists_bound_of_continuous (etaK_contDiff n).continuous
  exact ⟨C, fun s => by simpa using hC s⟩

/-- The cut-off primitive `r ↦ ∫_r^{δ n} etaK n`. -/
noncomputable def thetaK (n : ℕ) (r : ℝ) : ℝ := ∫ s in r..tDelta n, etaK n s

theorem thetaK_hasDerivAt (n : ℕ) (r : ℝ) : HasDerivAt (thetaK n) (-etaK n r) r := by
  have h := intervalIntegral.integral_hasDerivAt_left (f := etaK n) (a := r) (b := tDelta n)
    ((etaK_integrable n).intervalIntegrable) ((etaK_contDiff n).continuous.stronglyMeasurableAtFilter _ _)
    (etaK_contDiff n).continuous.continuousAt
  exact h

theorem thetaK_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (thetaK n) := by
  rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) = (∞ : WithTop ℕ∞) from rfl, contDiff_infty_iff_deriv]
  refine ⟨fun r => (thetaK_hasDerivAt n r).differentiableAt, ?_⟩
  have : deriv (thetaK n) = fun r => -etaK n r := funext fun r => (thetaK_hasDerivAt n r).deriv
  rw [this]
  exact (etaK_contDiff n).neg

theorem deriv_thetaK (n : ℕ) (r : ℝ) : deriv (thetaK n) r = -etaK n r := (thetaK_hasDerivAt n r).deriv

theorem thetaK_eq_zero (n : ℕ) {r : ℝ} (hr : tDelta n ≤ r) : thetaK n r = 0 := by
  unfold thetaK
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  have : ∫ s in tDelta n..r, etaK n s = 0 := by
    refine intervalIntegral.integral_zero_ae ?_
    refine Filter.Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le hr] at hs
    exact etaK_eq_zero n (by rw [abs_of_pos (lt_of_lt_of_le (tDelta_pos n) hs.1.le)]; exact hs.1.le)
  exact this

theorem integral_Ioi_etaK_even (n : ℕ) : ∫ s in Set.Ioi (0:ℝ), etaK n s = 1 / 2 := by
  have h1 : ∫ s in Set.Ioi (0:ℝ), etaK n s = ∫ s in Set.Iic (0:ℝ), etaK n s := by
    have := integral_comp_neg_Ioi (c := (0:ℝ)) (etaK n)
    simp only [etaK_neg, neg_zero] at this
    exact this
  have h2 := integral_add_compl (s := Set.Ioi (0:ℝ)) measurableSet_Ioi (etaK_integrable n)
  rw [etaK_integral, compl_Ioi] at h2
  linarith

theorem thetaK_zero (n : ℕ) : thetaK n 0 = 1 / 2 := by
  unfold thetaK
  rw [intervalIntegral.integral_of_le (tDelta_pos n).le]
  rw [← integral_Ioi_etaK_even n]
  have hsub : ∫ s in Set.Ioc 0 (tDelta n), etaK n s = ∫ s in Set.Ioi (0:ℝ), etaK n s := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self]
    intro s hs
    exact etaK_eq_zero n (by
      have : tDelta n < s := by
        by_contra h
        exact hs.2 ⟨hs.1, not_lt.mp h⟩
      rw [abs_of_pos (lt_trans (tDelta_pos n) this)]; exact this.le)
  exact hsub

theorem thetaK_eq_one (n : ℕ) {r : ℝ} (hr : r ≤ -tDelta n) : thetaK n r = 1 := by
  unfold thetaK
  have h1 : ∫ s in r..tDelta n, etaK n s = ∫ s, etaK n s := by
    rw [intervalIntegral.integral_of_le (by linarith [tDelta_pos n])]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc r (tDelta n)) ?_)
    intro s hs
    have : s ≤ r ∨ tDelta n < s := by
      by_contra h
      push Not at h
      exact hs ⟨h.1, h.2⟩
    rcases this with h | h
    · exact etaK_eq_zero n (by rw [abs_of_nonpos (by linarith [tDelta_pos n])]; linarith)
    · exact etaK_eq_zero n (by rw [abs_of_pos (lt_trans (tDelta_pos n) h)]; exact h.le)
  rw [h1, etaK_integral]

theorem thetaK_nonneg (n : ℕ) (r : ℝ) : 0 ≤ thetaK n r := by
  by_cases h : r ≤ tDelta n
  · exact intervalIntegral.integral_nonneg h (fun s _ => etaK_nonneg n s)
  · push Not at h
    have h0 := thetaK_eq_zero n h.le
    unfold thetaK at h0 ⊢
    rw [h0]

theorem thetaK_le_one (n : ℕ) (r : ℝ) : thetaK n r ≤ 1 := by
  have hm : Antitone (thetaK n) := by
    refine antitone_of_deriv_nonpos (fun r => (thetaK_hasDerivAt n r).differentiableAt) ?_
    intro r
    rw [deriv_thetaK]
    linarith [etaK_nonneg n r]
  by_cases h : r ≤ -tDelta n
  · rw [thetaK_eq_one n h]
  · push Not at h
    calc thetaK n r ≤ thetaK n (-tDelta n) := hm (by linarith)
      _ = 1 := thetaK_eq_one n le_rfl

end PDE
