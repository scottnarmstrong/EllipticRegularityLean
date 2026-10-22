module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Smooth radial profiles approximating the kink profile

Manuscript Theorem 4.24, Step 4, is the integration of `r φ' ≥ β φ` between two
radii. In the integrated formulation it amounts to testing the differential
inequality with the Lipschitz profile `(max(t, a²)^{-r} - b^{-2r}) / (2 r)`
(`t = |x|²`, `r = β / 2`), which we approximate by smooth nonincreasing
profiles
`H_n(t) = ∫_t^{b²} ½ s^{-r-1} χ_n(s) ds`,
where `χ_n` are smooth cutoffs of `(a², b²)` built from `Real.smoothTransition`.
This file records the one-variable facts: smoothness, sign, support, uniform
bounds, and the pointwise limits of `H_n` and of `-H_n' = ½ s^{-r-1} χ_n`.
-/

@[expose] public section

namespace PDE.Ch4Spagnolo

open MeasureTheory Set Filter
open scoped Topology

section Profiles

variable (r A0 B0 : ℝ)

/-- Smooth cutoffs converging to the indicator of `(A₀, B₀)`. -/
noncomputable def cutoffSeq (n : ℕ) (s : ℝ) : ℝ :=
  Real.smoothTransition ((n + 1) * (s - A0)) * Real.smoothTransition ((n + 1) * (B0 - s))

/-- The weights `½ s^{-r-1} χ_n(s)`. -/
noncomputable def weightSeq (n : ℕ) (s : ℝ) : ℝ :=
  1 / 2 * s ^ (-r - 1) * cutoffSeq A0 B0 n s

/-- The profiles `H_n(t) = ∫_t^{B₀} ½ s^{-r-1} χ_n(s) ds`. -/
noncomputable def profileSeq (n : ℕ) (t : ℝ) : ℝ :=
  -∫ s in B0..t, weightSeq r A0 B0 n s

/-- The limit weight `½ s^{-r-1} 1_{(A₀, B₀)}(s)`. -/
noncomputable def weightLim (s : ℝ) : ℝ :=
  if s ∈ Ioo A0 B0 then 1 / 2 * s ^ (-r - 1) else 0

/-- The limit (kink) profile. -/
noncomputable def profileLim (t : ℝ) : ℝ :=
  if t ≤ B0 then ((max t A0) ^ (-r) - B0 ^ (-r)) / (2 * r) else 0

variable {r A0 B0}

theorem cutoffSeq_nonneg (n : ℕ) (s : ℝ) : 0 ≤ cutoffSeq A0 B0 n s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem cutoffSeq_le_one (n : ℕ) (s : ℝ) : cutoffSeq A0 B0 n s ≤ 1 := by
  unfold cutoffSeq
  calc _ ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _)
          (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem cutoffSeq_eq_zero_of_le (n : ℕ) {s : ℝ} (hs : s ≤ A0) : cutoffSeq A0 B0 n s = 0 := by
  unfold cutoffSeq
  rw [Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by linarith)), zero_mul]

theorem cutoffSeq_eq_zero_of_ge (n : ℕ) {s : ℝ} (hs : B0 ≤ s) : cutoffSeq A0 B0 n s = 0 := by
  unfold cutoffSeq
  rw [Real.smoothTransition.zero_of_nonpos (x := ((n : ℝ) + 1) * (B0 - s))
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)), mul_zero]

theorem contDiff_cutoffSeq (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffSeq A0 B0 n) := by
  unfold cutoffSeq
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul
    (contDiff_id.sub contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

private theorem eventually_one_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ ((n : ℝ) + 1) * c := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * c) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const hc
  exact h.eventually_ge_atTop 1

theorem tendsto_cutoffSeq {s : ℝ} (hs : s ∈ Ioo A0 B0) :
    Tendsto (fun n => cutoffSeq A0 B0 n s) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_one_le_mul (sub_pos.2 hs.1),
    eventually_one_le_mul (sub_pos.2 hs.2)] with n h1 h2
  unfold cutoffSeq
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem weightSeq_eq_zero_of_le (n : ℕ) {s : ℝ} (hs : s ≤ A0) : weightSeq r A0 B0 n s = 0 := by
  simp [weightSeq, cutoffSeq_eq_zero_of_le n hs]

theorem weightSeq_eq_zero_of_ge (n : ℕ) {s : ℝ} (hs : B0 ≤ s) : weightSeq r A0 B0 n s = 0 := by
  simp [weightSeq, cutoffSeq_eq_zero_of_ge n hs]

theorem weightSeq_nonneg (hA0 : 0 < A0) (n : ℕ) (s : ℝ) : 0 ≤ weightSeq r A0 B0 n s := by
  rcases le_or_gt s A0 with hs | hs
  · rw [weightSeq_eq_zero_of_le n hs]
  · exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
      (cutoffSeq_nonneg n s)

theorem weightSeq_le (hr : 0 < r) (hA0 : 0 < A0) (n : ℕ) (s : ℝ) :
    weightSeq r A0 B0 n s ≤ 1 / 2 * A0 ^ (-r - 1) := by
  rcases le_or_gt s A0 with hs | hs
  · rw [weightSeq_eq_zero_of_le n hs]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hA0.le _)
  · have hpow : s ^ (-r - 1) ≤ A0 ^ (-r - 1) :=
      Real.rpow_le_rpow_of_nonpos hA0 hs.le (by linarith)
    unfold weightSeq
    calc 1 / 2 * s ^ (-r - 1) * cutoffSeq A0 B0 n s ≤ 1 / 2 * s ^ (-r - 1) * 1 :=
          mul_le_mul_of_nonneg_left (cutoffSeq_le_one n s)
            (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
      _ ≤ 1 / 2 * A0 ^ (-r - 1) := by nlinarith

theorem contDiff_weightSeq (hA0 : 0 < A0) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (weightSeq r A0 B0 n) := by
  refine contDiff_iff_contDiffAt.2 fun s => ?_
  rcases lt_or_ge s A0 with hs | hs
  · have hev : weightSeq r A0 B0 n =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      exact weightSeq_eq_zero_of_le n (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs0 : s ≠ 0 := (lt_of_lt_of_le hA0 hs).ne'
    unfold weightSeq
    exact (contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hs0)).mul
      (contDiff_cutoffSeq n).contDiffAt

theorem tendsto_weightSeq (s : ℝ) :
    Tendsto (fun n => weightSeq r A0 B0 n s) atTop (𝓝 (weightLim r A0 B0 s)) := by
  unfold weightLim
  split_ifs with hs
  · have h := (tendsto_cutoffSeq hs).const_mul (1 / 2 * s ^ (-r - 1))
    rw [mul_one] at h
    exact h
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    simp only [mem_Ioo, not_and_or, not_lt] at hs
    rcases hs with hs | hs
    · exact (weightSeq_eq_zero_of_le n hs).symm
    · exact (weightSeq_eq_zero_of_ge n hs).symm

theorem hasDerivAt_profileSeq (hA0 : 0 < A0) (n : ℕ) (t : ℝ) :
    HasDerivAt (profileSeq r A0 B0 n) (-weightSeq r A0 B0 n t) t :=
  ((contDiff_weightSeq hA0 n).continuous.integral_hasStrictDerivAt B0 t).hasDerivAt.neg

theorem deriv_profileSeq (hA0 : 0 < A0) (n : ℕ) (t : ℝ) :
    deriv (profileSeq r A0 B0 n) t = -weightSeq r A0 B0 n t :=
  (hasDerivAt_profileSeq hA0 n t).deriv

theorem contDiff_profileSeq (hA0 : 0 < A0) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (profileSeq r A0 B0 n) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun t => (hasDerivAt_profileSeq hA0 n t).differentiableAt,
    ?_⟩
  have : deriv (profileSeq r A0 B0 n) = fun t => -weightSeq r A0 B0 n t :=
    funext (deriv_profileSeq hA0 n)
  rw [this]
  exact (contDiff_weightSeq hA0 n).neg

theorem profileSeq_eq_zero_of_ge (n : ℕ) {t : ℝ} (ht : B0 ≤ t) : profileSeq r A0 B0 n t = 0 := by
  unfold profileSeq
  have : ∀ s ∈ uIcc B0 t, weightSeq r A0 B0 n s = 0 := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact weightSeq_eq_zero_of_ge n hs.1
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) this]
  simp

theorem profileSeq_eq_integral (hA0 : 0 < A0) (n : ℕ) {t : ℝ} :
    profileSeq r A0 B0 n t = ∫ s in (max t A0)..B0, weightSeq r A0 B0 n s := by
  unfold profileSeq
  rw [← intervalIntegral.integral_symm]
  rcases le_or_gt A0 t with ht | ht
  · rw [max_eq_left ht]
  · rw [max_eq_right ht.le]
    have hcont := (contDiff_weightSeq (r := r) (B0 := B0) hA0 n).continuous
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := A0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have : ∀ s ∈ uIcc t A0, weightSeq r A0 B0 n s = 0 := by
      intro s hs
      rw [uIcc_of_le ht.le] at hs
      exact weightSeq_eq_zero_of_le n hs.2
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) this]
    simp

theorem abs_profileSeq_le (hr : 0 < r) (hA0 : 0 < A0) (hB0 : 0 < B0) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : |profileSeq r A0 B0 n t| ≤ 1 / 2 * A0 ^ (-r - 1) * B0 := by
  have hK : 0 ≤ 1 / 2 * A0 ^ (-r - 1) := mul_nonneg (by norm_num) (Real.rpow_nonneg hA0.le _)
  rcases le_or_gt B0 t with htB | htB
  · rw [profileSeq_eq_zero_of_ge n htB, abs_zero]
    exact mul_nonneg hK hB0.le
  · unfold profileSeq
    rw [abs_neg]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := B0) (b := t)
      (C := 1 / 2 * A0 ^ (-r - 1)) (f := weightSeq r A0 B0 n) fun s _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (weightSeq_nonneg hA0 n s)]
        exact weightSeq_le hr hA0 n s
    rw [Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith

theorem tendsto_profileSeq (hr : 0 < r) (hA0 : 0 < A0) (hAB : A0 ≤ B0) (t : ℝ) :
    Tendsto (fun n => profileSeq r A0 B0 n t) atTop (𝓝 (profileLim r A0 B0 t)) := by
  unfold profileLim
  split_ifs with htB
  · have hmA : A0 ≤ max t A0 := le_max_right _ _
    have hmB0 : max t A0 ≤ B0 := max_le htB hAB
    simp only [profileSeq_eq_integral (r := r) (B0 := B0) hA0]
    generalize max t A0 = m at hmA hmB0 ⊢
    have hm0 : 0 < m := lt_of_lt_of_le hA0 hmA
    rcases eq_or_lt_of_le hmB0 with hmB | hmB
    · rw [hmB]
      simp only [intervalIntegral.integral_same, sub_self, zero_div]
      exact tendsto_const_nhds
    · have hae : ∀ᵐ s ∂volume, s ∈ uIoc m B0 →
          Tendsto (fun n => weightSeq r A0 B0 n s) atTop (𝓝 (1 / 2 * s ^ (-r - 1))) := by
        filter_upwards [(countable_singleton B0).ae_notMem volume] with s hsB hs
        rw [uIoc_of_le hmB.le] at hs
        have hsIoo : s ∈ Ioo A0 B0 :=
          ⟨lt_of_le_of_lt hmA hs.1, lt_of_le_of_ne hs.2 hsB⟩
        have h := tendsto_weightSeq (r := r) (A0 := A0) (B0 := B0) s
        simpa only [weightLim, hsIoo, ↓reduceIte] using h
      have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (a := m) (b := B0) (l := atTop)
        (F := fun n s => weightSeq r A0 B0 n s) (f := fun s => 1 / 2 * s ^ (-r - 1))
        (fun _ => 1 / 2 * A0 ^ (-r - 1))
        (Eventually.of_forall fun n =>
          (contDiff_weightSeq hA0 n).continuous.aestronglyMeasurable)
        (Eventually.of_forall fun n => Eventually.of_forall fun s _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (weightSeq_nonneg hA0 n s)]
          exact weightSeq_le hr hA0 n s)
        intervalIntegrable_const hae
      have hval : ∫ s in m..B0, 1 / 2 * s ^ (-r - 1) = (m ^ (-r) - B0 ^ (-r)) / (2 * r) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
        · rw [show -r - 1 + 1 = -r by ring]
          field_simp
          ring
        · rw [uIcc_of_le hmB.le]
          exact fun h => absurd h.1 (not_le.2 hm0)
      rw [hval] at hlim
      exact hlim
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    exact (profileSeq_eq_zero_of_ge n (le_of_lt (not_le.1 htB))).symm

end Profiles

end PDE.Ch4Spagnolo
