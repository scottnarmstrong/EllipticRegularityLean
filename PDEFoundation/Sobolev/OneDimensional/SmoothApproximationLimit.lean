module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Sobolev.OneDimensional.UniformLimit
public import PDEFoundation.Sobolev.OneDimensional.WeakClosure

/-!
# Smooth approximation limits on an interval

This module packages the one-dimensional passage from smooth approximants to
a continuous representative with a weak derivative.  The hypotheses retain
the actual value and derivative error functions in `L²`; convergence of their
displayed squared integrals is therefore not interpreted through a zero
integral of a nonintegrable function.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- Smooth scalar approximants whose value and derivative errors converge in
the explicit interval `L²` energies have a canonical continuous limit.  The
limit agrees almost everywhere on the closed interval with the supplied value
data and has the supplied derivative data as a weak derivative on the open
interval. -/
theorem uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_error
    {a b : ℝ} (hab : a < b)
    {F : ℕ → ℝ → ℝ} {u g : ℝ → ℝ}
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hValueError : ∀ n, MemLp (fun t => F n t - u t) 2
      (volume.restrict (Icc a b)))
    (hDerivError : ∀ n, MemLp (fun t => deriv (F n) t - g t) 2
      (volume.restrict (Icc a b)))
    (hValue : Tendsto
      (fun n => ∫ t in Icc a b, |F n t - u t| ^ 2) atTop (𝓝 0))
    (hDeriv : Tendsto
      (fun n => ∫ t in Icc a b, |deriv (F n) t - g t| ^ (2 : ℝ))
        atTop (𝓝 0)) :
    TendstoUniformlyOn F (uniformCauchySeqLimit F) atTop (Icc a b) ∧
      ContinuousOn (uniformCauchySeqLimit F) (Icc a b) ∧
      uniformCauchySeqLimit F =ᵐ[volume.restrict (Icc a b)] u ∧
      HasWeakDerivOnIoo a b (uniformCauchySeqLimit F) g := by
  have hValueIntegrable : ∀ n,
      IntegrableOn (fun t => |F n t - u t| ^ 2) (Icc a b) := by
    intro n
    simpa only [IntegrableOn, sq_abs] using (hValueError n).integrable_sq
  have hDerivIntegrable : ∀ n,
      IntegrableOn (fun t => |deriv (F n) t - g t| ^ (2 : ℝ)) (Icc a b) := by
    intro n
    simpa only [IntegrableOn, Real.rpow_two, sq_abs] using
      (hDerivError n).integrable_sq
  have hUniform : UniformCauchySeqOn F atTop (Icc a b) := by
    exact uniformCauchySeqOn_of_tendsto_setIntegral_sq_error hab hF
      hValueIntegrable hDerivIntegrable hValue hDeriv
  have hUniformTendsto :
      TendstoUniformlyOn F (uniformCauchySeqLimit F) atTop (Icc a b) :=
    tendstoUniformlyOn_uniformCauchySeqLimit hUniform
  have hContinuous : ContinuousOn (uniformCauchySeqLimit F) (Icc a b) :=
    continuousOn_uniformCauchySeqLimit hUniform
      (fun n => (hF n).continuous.continuousOn)
  have hFMem : ∀ n, MemLp (F n) 2 (volume.restrict (Icc a b)) := by
    intro n
    exact memLp_two_on_Icc_of_continuous (hF n).continuous
  have hLimitMem : MemLp (uniformCauchySeqLimit F) 2
      (volume.restrict (Icc a b)) := by
    have hmeas : AEStronglyMeasurable (uniformCauchySeqLimit F)
        (volume.restrict (Icc a b)) :=
      hContinuous.aestronglyMeasurable measurableSet_Icc
    exact (memLp_two_iff_integrable_sq hmeas).2
      ((hContinuous.pow 2).integrableOn_Icc)
  have hValueLp : Tendsto
      (fun n => eLpNorm (fun t => F n t - u t) 2
        (volume.restrict (Icc a b))) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_tendsto_integral_sq hValueError
    simpa only [Pi.sub_apply, sq_abs] using hValue
  have hLimitLp : Tendsto
      (fun n => eLpNorm (F n - uniformCauchySeqLimit F) 2
        (volume.restrict (Icc a b))) atTop (𝓝 0) :=
    tendsto_eLpNorm_sub_uniformCauchySeqLimit_two_on_Icc hUniform
      (fun n => (hFMem n).aestronglyMeasurable)
  have hAe : uniformCauchySeqLimit F =ᵐ[volume.restrict (Icc a b)] u := by
    exact ae_eq_of_tendsto_eLpNorm_sub (by norm_num)
      (fun n => (hFMem n).aestronglyMeasurable)
      hLimitMem.aestronglyMeasurable hu.aestronglyMeasurable hLimitLp hValueLp
  have hWeakSmooth : ∀ n,
      HasWeakDerivOnIoo a b (F n) (fun t => deriv (F n) t) := by
    intro n
    exact HasWeakDerivOnIoo.of_contDiff (hF n)
  have hOpenSubset : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  have huOpen : MemLp u 2 (volume.restrict (Ioo a b)) :=
    hu.mono_measure (Measure.restrict_mono hOpenSubset le_rfl)
  have hgOpen : MemLp g 2 (volume.restrict (Ioo a b)) :=
    hg.mono_measure (Measure.restrict_mono hOpenSubset le_rfl)
  have hLimitOpen : MemLp (uniformCauchySeqLimit F) 2
      (volume.restrict (Ioo a b)) :=
    hLimitMem.mono_measure (Measure.restrict_mono hOpenSubset le_rfl)
  have hFOpen : ∀ n, MemLp (F n) 2 (volume.restrict (Ioo a b)) := fun n =>
    (hFMem n).mono_measure (Measure.restrict_mono hOpenSubset le_rfl)
  have hDerivOpen : ∀ n, MemLp (fun t => deriv (F n) t) 2
      (volume.restrict (Ioo a b)) := by
    intro n
    have hmem : MemLp (deriv (F n)) 2 (volume.restrict (Icc a b)) :=
      memLp_two_on_Icc_of_continuous (hF n).continuous_deriv_one
    exact hmem.mono_measure (Measure.restrict_mono hOpenSubset le_rfl)
  have hValueOpen : Tendsto
      (fun n => eLpNorm (fun t => F n t - u t) 2
        (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun n => (hValueError n).mono_measure
        (Measure.restrict_mono hOpenSubset le_rfl))
    simpa only [Pi.sub_apply, sq_abs, integral_Icc_eq_integral_Ioo] using hValue
  have hDerivOpenLp : Tendsto
      (fun n => eLpNorm (fun t => deriv (F n) t - g t) 2
        (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun n => (hDerivError n).mono_measure
        (Measure.restrict_mono hOpenSubset le_rfl))
    simpa only [Pi.sub_apply, Real.rpow_two, sq_abs,
      integral_Icc_eq_integral_Ioo] using hDeriv
  have hLimitOpenLp : Tendsto
      (fun n => eLpNorm (fun t => F n t - uniformCauchySeqLimit F t) 2
        (volume.restrict (Ioo a b))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hLimitLp
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    exact Filter.Eventually.of_forall fun n =>
      eLpNorm_mono_measure _ (Measure.restrict_mono hOpenSubset le_rfl)
  have hWeak : HasWeakDerivOnIoo a b (uniformCauchySeqLimit F) g :=
    HasWeakDerivOnIoo.of_tendsto_eLpNorm
      hLimitOpen hgOpen hFOpen hDerivOpen hWeakSmooth hLimitOpenLp hDerivOpenLp
  exact ⟨hUniformTendsto, hContinuous, hAe, hWeak⟩

end

end PDE
