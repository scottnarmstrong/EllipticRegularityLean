module

public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify
public import PDEFoundation.Measure.LpPower

/-!
# Mollification of bounded compactly supported scalar functions

For `f` measurable, bounded, and vanishing outside a bounded set (`BddSupp f`), the whole-space
mollification `wholeSpaceMollify a f` (convolution with the scaled unit kernel, supported in the
sup-norm ball of radius `a`) is smooth, compactly supported, linear in `f`, preserves the integral
and does not increase the `L¹` and `L²` norms.
-/

@[expose] public section

open MeasureTheory
open scoped Convolution ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- Measurable, bounded, and vanishing outside a bounded set. -/
structure BddSupp (f : Vec d → ℝ) : Prop where
  meas : Measurable f
  bdd : ∃ C, ∀ x, |f x| ≤ C
  supp : ∃ R, ∀ x, R ≤ ‖x‖ → f x = 0

namespace BddSupp

theorem memLp {f : Vec d → ℝ} (hf : BddSupp f) (p : ℝ≥0∞) : MemLp f p volume := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨R, hR⟩ := hf.supp
  have hg : MemLp ((Metric.closedBall (0 : Vec d) R).indicator (fun _ => C)) p volume :=
    (memLp_indicator_const p (measurableSet_closedBall) C
      (Or.inr (measure_closedBall_lt_top.ne)))
  refine hg.mono' hf.meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Metric.closedBall (0 : Vec d) R
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hC x
  · have : f x = 0 := hR x (by
      by_contra h
      push Not at h
      exact hx (by simpa using h.le))
    rw [this, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (abs_nonneg _).trans (hC 0)) x

theorem integrable {f : Vec d → ℝ} (hf : BddSupp f) : Integrable f volume :=
  memLp_one_iff_integrable.mp (hf.memLp 1)

theorem add {f g : Vec d → ℝ} (hf : BddSupp f) (hg : BddSupp g) : BddSupp (f + g) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨C', hC'⟩ := hg.bdd
  obtain ⟨R, hR⟩ := hf.supp
  obtain ⟨R', hR'⟩ := hg.supp
  refine ⟨hf.meas.add hg.meas, ⟨C + C', fun x => ?_⟩, ⟨max R R', fun x hx => ?_⟩⟩
  · exact (abs_add_le _ _).trans (add_le_add (hC x) (hC' x))
  · simp [hR x ((le_max_left _ _).trans hx), hR' x ((le_max_right _ _).trans hx)]

theorem neg {f : Vec d → ℝ} (hf : BddSupp f) : BddSupp (-f) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨R, hR⟩ := hf.supp
  exact ⟨hf.meas.neg, ⟨C, fun x => by simpa using hC x⟩, ⟨R, fun x hx => by simp [hR x hx]⟩⟩

theorem sub {f g : Vec d → ℝ} (hf : BddSupp f) (hg : BddSupp g) : BddSupp (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem zero : BddSupp (0 : Vec d → ℝ) :=
  ⟨measurable_const, ⟨0, fun x => by simp⟩, ⟨0, fun x _ => rfl⟩⟩

theorem finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℝ} (hf : ∀ i ∈ s, BddSupp (f i)) :
    BddSupp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end BddSupp

/-- The scaled unit kernel. -/
abbrev mollK (a : ℝ) : Vec d → ℝ :=
  scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a

theorem wholeSpaceMollify_apply (a : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    wholeSpaceMollify a f x = ∫ t, mollK a t * f (x - t) := by
  simp [wholeSpaceMollify, convolution_def]

theorem convolutionExists_mollK {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) :
    ConvolutionExists (mollK a) f (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  (hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport ha).convolutionExists_left
    _ (continuous_scaledConvexApproxKernel
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous a) hf

theorem wholeSpaceMollify_add {a : ℝ} (ha : 0 < a) {f g : Vec d → ℝ} (hf : BddSupp f)
    (hg : BddSupp g) :
    wholeSpaceMollify a (f + g) = wholeSpaceMollify a f + wholeSpaceMollify a g := by
  have e1 := convolutionExists_mollK ha (hf.integrable.locallyIntegrable)
  have e2 := convolutionExists_mollK ha (hg.integrable.locallyIntegrable)
  simpa [wholeSpaceMollify] using e1.distrib_add e2

theorem wholeSpaceMollify_sub {a : ℝ} (ha : 0 < a) {f g : Vec d → ℝ} (hf : BddSupp f)
    (hg : BddSupp g) :
    wholeSpaceMollify a (f - g) = wholeSpaceMollify a f - wholeSpaceMollify a g := by
  have h := wholeSpaceMollify_add ha (hf.sub hg) hg
  rw [sub_add_cancel] at h
  rw [h]; abel

theorem wholeSpaceMollify_finsetSum {a : ℝ} (ha : 0 < a) {ι : Type*} (s : Finset ι)
    {f : ι → Vec d → ℝ} (hf : ∀ i ∈ s, BddSupp (f i)) :
    wholeSpaceMollify a (∑ i ∈ s, f i) = ∑ i ∈ s, wholeSpaceMollify a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext x
    simp [wholeSpaceMollify_apply]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      wholeSpaceMollify_add ha (hf i (Finset.mem_insert_self _ _))
        (BddSupp.finsetSum s fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem wholeSpaceMollify_eq_zero {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} {x : Vec d}
    (h : ∀ t : Vec d, ‖t‖ ≤ a → f (x - t) = 0) : wholeSpaceMollify a f x = 0 := by
  rw [wholeSpaceMollify_apply]
  have : ∀ t, mollK a t * f (x - t) = 0 := by
    intro t
    by_cases ht : a < ‖t‖
    · simp [scaledUnitKernel_eq_zero_of_lt_norm ha ht]
    · simp [h t (not_lt.mp ht)]
  simp [this]

theorem contDiff_wholeSpaceMollify {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeSpaceMollify a f) :=
  (contDiff_memLp_convolution_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha le_rfl ENNReal.one_ne_top
    (hf.memLp 1)).1

theorem hasCompactSupport_wholeSpaceMollify {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : BddSupp f) : HasCompactSupport (wholeSpaceMollify a f) := by
  obtain ⟨R, hR⟩ := hf.supp
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) (R + a)) fun x hx => ?_
  refine wholeSpaceMollify_eq_zero ha fun t ht => hR _ ?_
  have hx' : R + a < ‖x‖ := by simpa using hx
  have : ‖x‖ ≤ ‖x - t‖ + ‖t‖ := by simpa using norm_add_le (x - t) t
  linarith

theorem bddSupp_wholeSpaceMollify {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f) :
    BddSupp (wholeSpaceMollify a f) := by
  have hc := contDiff_wholeSpaceMollify ha hf
  have hcs := hasCompactSupport_wholeSpaceMollify ha hf
  obtain ⟨C, hC⟩ := hc.continuous.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨hc.continuous.measurable, ⟨C, hC⟩, ⟨R + 1, fun x hx => ?_⟩⟩
  by_contra hne
  have := hR (subset_tsupport _ hne)
  have h2 : ‖x‖ ≤ R := by simpa using this
  linarith

theorem integral_wholeSpaceMollify {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f) :
    ∫ x, wholeSpaceMollify a f x = ∫ x, f x := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have := integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (ν := volume)
    (integrable_scaledConvexApproxKernel hρ ha) hf.integrable
  simpa [wholeSpaceMollify, integral_scaledConvexApproxKernel hρ ha] using this

theorem eLpNorm_wholeSpaceMollify_le {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    eLpNorm (wholeSpaceMollify a f) p volume ≤ eLpNorm f p volume :=
  (contDiff_memLp_convolution_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha hp hpTop (hf.memLp p)).2.2

theorem integral_sq_wholeSpaceMollify_le {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f) :
    ∫ x, wholeSpaceMollify a f x ^ 2 ≤ ∫ x, f x ^ 2 := by
  have hg := (bddSupp_wholeSpaceMollify ha hf).memLp 2
  have h := eLpNorm_wholeSpaceMollify_le ha hf (p := 2) (by norm_num) (by simp)
  rw [← toReal_eLpNorm_two_sq_eq_integral_sq hg, ← toReal_eLpNorm_two_sq_eq_integral_sq (hf.memLp 2)]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (hf.memLp 2).eLpNorm_lt_top.ne h) 2

theorem integral_abs_wholeSpaceMollify_le {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ} (hf : BddSupp f) :
    ∫ x, |wholeSpaceMollify a f x| ≤ ∫ x, |f x| := by
  have hg := bddSupp_wholeSpaceMollify ha hf
  have h := eLpNorm_wholeSpaceMollify_le ha hf (p := 1) le_rfl (by simp)
  rw [eLpNorm_one_eq_lintegral_enorm hg.meas.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.meas.aestronglyMeasurable] at h
  have h1 := ofReal_integral_norm_eq_lintegral_enorm hg.integrable
  have h2 := ofReal_integral_norm_eq_lintegral_enorm hf.integrable
  simp only [Real.norm_eq_abs] at h1 h2
  rw [← h1, ← h2] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => abs_nonneg _)).mp h

end

end PDE.NewtonWeakType
