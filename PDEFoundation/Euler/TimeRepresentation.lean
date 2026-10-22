module

public import PDEFoundation.Euler.TimeKernel
public import PDEFoundation.Euler.TimeDiag
public import PDEFoundation.Euler.TimeProduct

/-!
# Distributional time derivative to integral representation

If `f, R ∈ L¹(0,T)` satisfy `∫ χ' f + ∫ χ R + χ(0) D₀ = 0` for all smooth `χ` vanishing near `T`
(i.e. `f' = R` on `[0,T)` with `f(0) = D₀`), then `f(t) = D₀ + ∫₀ᵗ R` for a.e. `t`.
The test functions are `χ(τ) = thetaK n (τ - t)` (smoothed indicator of `(-∞,t)`), and the limit `n → ∞` is a
Lebesgue point argument (`ae_tendsto_timeMollify`) and dominated convergence.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem hasDerivAt_thetaK_comp (n : ℕ) (t τ : ℝ) :
    HasDerivAt (fun τ => thetaK n (τ - t)) (-etaK n (τ - t)) τ := by
  have h1 := (thetaK_hasDerivAt n (τ - t))
  have h2 := h1.comp τ ((hasDerivAt_id τ).sub_const t)
  convert h2 using 1
  · rfl
  · ring

theorem ae_eq_of_weak_derivative {T : ℝ} {f R : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 T)) (hR : IntegrableOn R (Icc 0 T)) {D0 : ℝ}
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → ∀ b, b < T → (∀ τ, b ≤ τ → χ τ = 0) →
      (∫ τ in Icc (0 : ℝ) T, deriv χ τ * f τ) + (∫ τ in Icc (0 : ℝ) T, χ τ * R τ) + χ 0 * D0 = 0) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), f t = D0 + ∫ τ in Icc 0 t, R τ := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  set f' : ℝ → ℝ := (Icc (0 : ℝ) T).indicator f with hf'
  have hfloc : LocallyIntegrable f' volume := by
    have : Integrable f' volume := (integrable_indicator_iff measurableSet_Icc).2 hf
    exact this.locallyIntegrable
  have hleb := ae_tendsto_timeMollify hfloc
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := (Set.countable_singleton (0 : ℝ)).ae_notMem _
  have hneT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T := (Set.countable_singleton T).ae_notMem _
  filter_upwards [ae_restrict_of_ae hleb, ae_restrict_of_ae hne0, ae_restrict_of_ae hneT,
    ae_restrict_mem measurableSet_Icc] with t hlt ht0 htT htm
  have ht0' : 0 < t := lt_of_le_of_ne htm.1 (Ne.symm ht0)
  have htT' : t < T := lt_of_le_of_ne htm.2 htT
  -- the mollified `f` converges to `f t`
  have hA : Tendsto (fun n => ∫ τ, etaK n (τ - t) * f τ ∂ν) atTop (𝓝 (f t)) := by
    have hft : f' t = f t := by rw [hf', Set.indicator_of_mem htm]
    rw [hft] at hlt
    refine hlt.congr (fun n => ?_)
    rw [hν, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hf', Set.indicator_apply]
    split_ifs <;> simp
  -- the cut-off integral of `R` converges to `∫₀ᵗ R`
  have hR' : Integrable R ν := hR
  have hB : Tendsto (fun n => ∫ τ, thetaK n (τ - t) * R τ ∂ν) atTop
      (𝓝 (∫ τ in Icc 0 t, R τ)) := by
    have hlim := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun n τ => thetaK n (τ - t) * R τ) (f := fun τ => (Iio t).indicator R τ)
      (fun τ => |R τ|) (fun n => ((thetaK_contDiff n).continuous.comp
        (continuous_id.sub continuous_const)).aestronglyMeasurable.mul hR'.aestronglyMeasurable)
      hR'.abs ?_ ?_
    · have e : ∫ τ, (Iio t).indicator R τ ∂ν = ∫ τ in Icc 0 t, R τ := by
        rw [hν, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        have hs : Iio t ∩ Icc 0 T = Ico 0 t := by
          ext x
          simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
          constructor
          · intro hx; exact ⟨hx.2.1, hx.1⟩
          · intro hx; exact ⟨hx.2, hx.1, by linarith [hx.2]⟩
        rw [hs, integral_Icc_eq_integral_Ico]
      rw [e] at hlim
      exact hlim
    · intro n
      refine Filter.Eventually.of_forall fun τ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (thetaK_nonneg n _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (thetaK_le_one n _)
    · have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ t := (Set.countable_singleton t).ae_notMem _
      filter_upwards [ae_restrict_of_ae hne] with τ hτ
      rcases lt_or_gt_of_ne hτ with hlt' | hgt
      · have hev : ∀ᶠ n in atTop, tDelta n < t - τ := tendsto_tDelta.eventually (gt_mem_nhds (by linarith))
        rw [Set.indicator_of_mem (show τ ∈ Iio t from hlt')]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [thetaK_eq_one n (by linarith), one_mul]
      · have hev : ∀ᶠ n in atTop, tDelta n < τ - t := tendsto_tDelta.eventually (gt_mem_nhds (by linarith))
        rw [Set.indicator_of_notMem (show τ ∉ Iio t from not_lt.2 hgt.le)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [thetaK_eq_zero n (by linarith), zero_mul]
  -- the identity at level `n`
  have hev : ∀ᶠ n in atTop, tDelta n < T - t ∧ tDelta n ≤ t := by
    filter_upwards [tendsto_tDelta.eventually (gt_mem_nhds (sub_pos.2 htT')),
      tendsto_tDelta.eventually (gt_mem_nhds ht0')] with n h1 h2
    exact ⟨h1, h2.le⟩
  have hid : ∀ᶠ n in atTop, (∫ τ, etaK n (τ - t) * f τ ∂ν) =
      (∫ τ, thetaK n (τ - t) * R τ ∂ν) + D0 := by
    filter_upwards [hev] with n ⟨hn1, hn2⟩
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun τ => thetaK n (τ - t)) :=
      (thetaK_contDiff n).comp (contDiff_id.sub contDiff_const)
    have := h _ hχ (t + tDelta n) (by linarith) (fun τ hτ => thetaK_eq_zero n (by linarith))
    have hder : ∀ τ, deriv (fun τ => thetaK n (τ - t)) τ = -etaK n (τ - t) :=
      fun τ => (hasDerivAt_thetaK_comp n t τ).deriv
    simp only [hder, zero_sub] at this
    rw [thetaK_eq_one n (by linarith)] at this
    have e : ∀ τ, -etaK n (τ - t) * f τ = -(etaK n (τ - t) * f τ) := fun τ => by ring
    simp only [e, integral_neg] at this
    simp only [one_mul] at this
    linarith
  have := tendsto_nhds_unique (hA.congr' hid) (hB.add_const D0)
  linarith

end PDE
