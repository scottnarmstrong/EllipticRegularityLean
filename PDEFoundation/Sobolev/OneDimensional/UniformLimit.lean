module

public import PDEFoundation.Sobolev.OneDimensional.UniformControl
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Limits of uniformly Cauchy scalar sequences

This module packages the standard completeness argument used after the
one-dimensional `L²`--`C⁰` estimate: a uniformly Cauchy sequence of scalar
functions has a canonical pointwise limit, converges to it uniformly, and
passes continuity on the fixed set to that limit.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- The canonical pointwise limit of a scalar sequence.  The useful
convergence theorem below assumes that the sequence is uniformly Cauchy on
the set under consideration. -/
def uniformCauchySeqLimit {α : Type*} (F : ℕ → α → ℝ) (x : α) : ℝ :=
  limUnder atTop fun n => F n x

/-- A uniformly Cauchy scalar sequence converges uniformly on the set to its
canonical pointwise limit. -/
theorem tendstoUniformlyOn_uniformCauchySeqLimit
    {α : Type*} {F : ℕ → α → ℝ} {s : Set α}
    (hF : UniformCauchySeqOn F atTop s) :
    TendstoUniformlyOn F (uniformCauchySeqLimit F) atTop s := by
  apply hF.tendstoUniformlyOn_of_tendsto
  intro x hx
  exact (hF.cauchySeq hx).tendsto_limUnder

/-- If every term is continuous on the fixed set, then the canonical
uniform limit is continuous there as well. -/
theorem continuousOn_uniformCauchySeqLimit
    {α : Type*} [TopologicalSpace α] {F : ℕ → α → ℝ} {s : Set α}
    (hF : UniformCauchySeqOn F atTop s)
  (hContinuous : ∀ n, ContinuousOn (F n) s) :
    ContinuousOn (uniformCauchySeqLimit F) s :=
  (tendstoUniformlyOn_uniformCauchySeqLimit hF).continuousOn
    (Filter.Frequently.of_forall hContinuous)

/-- Uniform convergence on a bounded closed interval implies convergence in
the restricted `L²` seminorm.  The proof uses the exact finite-volume
supremum bound rather than a hidden compact-embedding theorem. -/
theorem tendsto_eLpNorm_sub_two_on_Icc_of_tendstoUniformlyOn
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hF : TendstoUniformlyOn F f atTop (Icc a b))
    (hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (F n - f) (volume.restrict (Icc a b))) :
    Tendsto
      (fun n =>
        eLpNorm (F n - f) 2
          (volume.restrict (Icc a b)))
      atTop (𝓝 0) := by
  let C : ℝ≥0∞ :=
    volume (Icc a b) ^ (1 / (2 : ℝ≥0∞).toReal)
  have hVolumeTop : volume (Icc a b) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hCTop : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · positivity
    · exact hVolumeTop
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδC⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt hCTop hε.ne'
  have hδReal : 0 < (δ : ℝ) := by
    exact_mod_cast hδ
  rw [Metric.tendstoUniformlyOn_iff] at hF
  filter_upwards [hF (δ : ℝ) hδReal, hmeas] with n hn hnmeas
  have hLp :
      eLpNorm (F n - f) 2
          (volume.restrict (Icc a b)) ≤
        (δ : ℝ≥0∞) * C := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc]
    have hbound :=
      eLpNorm_indicator_sub_le_of_dist_bdd
        (p := (2 : ℝ≥0∞)) volume
        (f := F n) (g := f)
        (c := (δ : ℝ))
        (by norm_num) measurableSet_Icc.nullMeasurableSet
        hδ.le ((aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hnmeas) (fun x hx => by
          simpa only [dist_comm] using (hn x hx).le)
    rw [ENNReal.ofReal_coe_nnreal] at hbound
    simpa only [C] using hbound
  exact hLp.trans hδC.le

/-- The canonical limit of a uniformly Cauchy sequence on a closed interval
is also its restricted `L²` limit. -/
theorem tendsto_eLpNorm_sub_uniformCauchySeqLimit_two_on_Icc
    {F : ℕ → ℝ → ℝ} {a b : ℝ}
    (hF : UniformCauchySeqOn F atTop (Icc a b))
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Icc a b))) :
    Tendsto
      (fun n =>
        eLpNorm (F n - uniformCauchySeqLimit F) 2
          (volume.restrict (Icc a b)))
      atTop (𝓝 0) := by
  have hU := tendstoUniformlyOn_uniformCauchySeqLimit hF
  have hlim : AEStronglyMeasurable (uniformCauchySeqLimit F)
      (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas
      ((ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun x hx => hU.tendsto_at hx))
  exact tendsto_eLpNorm_sub_two_on_Icc_of_tendstoUniformlyOn hU
    (Filter.Eventually.of_forall fun n => (hmeas n).sub hlim)

end

end PDE
