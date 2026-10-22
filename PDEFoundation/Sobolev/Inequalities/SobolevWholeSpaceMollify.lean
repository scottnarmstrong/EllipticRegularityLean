module

public import PDEFoundation.Measure.ProbabilityConvolutionLp
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Whole-space mollification in `L^p`

Convolution with the scaled unit kernel `scaledConvexApproxKernel
unitConvexApproxKernel a` on `Vec d`.  It is globally smooth, an `L^p`
contraction (`contDiff_memLp_convolution_scaledConvexApproxKernel`), and this
file proves the approximate-identity property `mollify a f → f` in `L^p` as
`a → 0`, `1 ≤ p < ∞`.
-/

@[expose] public section

open scoped ENNReal Convolution Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ}

/-- Whole-space mollification by the scaled unit kernel. -/
noncomputable def wholeSpaceMollify (a : ℝ) (f : Vec d → ℝ) : Vec d → ℝ :=
  scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem scaledUnitKernel_eq_zero_of_lt_norm {a : ℝ} (ha : 0 < a) {y : Vec d}
    (hy : a < ‖y‖) :
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a y = 0 := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hnorm : 1 < ‖a⁻¹ • y‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
    rw [← div_eq_inv_mul, lt_div_iff₀ ha]
    simpa using hy
  have hnot : a⁻¹ • y ∉ tsupport (unitConvexApproxKernel (d := d)) := fun hmem =>
    absurd (by simpa using hρ.support_subset_closedBall hmem) (not_le.mpr hnorm)
  simp [scaledConvexApproxKernel, image_eq_zero_of_notMem_tsupport hnot]

private theorem convolutionExists_scaledUnitKernel {a : ℝ} (ha : 0 < a)
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    ConvolutionExists
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  (hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport ha).convolutionExists_left
    _ (continuous_scaledConvexApproxKernel
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous a) hf

/-- Uniform approximation of a continuous compactly supported function. -/
theorem exists_forall_dist_wholeSpaceMollify_le {h : Vec d → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ x,
      dist (wholeSpaceMollify a h x) (h x) ≤ δ := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  obtain ⟨η, hη, hηh⟩ := Metric.uniformContinuous_iff.mp
    (hhc.uniformContinuous_of_continuous hh) δ hδ
  refine ⟨η / 2, half_pos hη, fun a ha haη x => ?_⟩
  set K := scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a with hK
  have hKnn : ∀ t, 0 ≤ K t := scaledConvexApproxKernel_nonneg hρ ha
  have hKint : Integrable K := integrable_scaledConvexApproxKernel hρ ha
  have hKone : ∫ t, K t = 1 := integral_scaledConvexApproxKernel hρ ha
  have hexists : Integrable (fun t => K t * h (x - t)) volume := by
    have := (convolutionExists_scaledUnitKernel ha
      (hh.locallyIntegrable (μ := volume))) x
    simpa [ConvolutionExistsAt] using this
  have hdiff : wholeSpaceMollify a h x - h x =
      ∫ t, K t * (h (x - t) - h x) := by
    have h1 : wholeSpaceMollify a h x = ∫ t, K t * h (x - t) := by
      simp [wholeSpaceMollify, convolution_def, ← hK]
    have h2 : h x = ∫ t, K t * h x := by
      rw [integral_mul_const, hKone, one_mul]
    rw [h1]
    conv_lhs => rw [h2]
    rw [← integral_sub hexists (hKint.mul_const _)]
    congr 1; ext t; ring
  rw [Real.dist_eq, hdiff]
  calc
    |∫ t, K t * (h (x - t) - h x)| ≤ ∫ t, K t * δ := by
      have := norm_integral_le_of_norm_le (μ := (volume : Measure (Vec d)))
        (f := fun t => K t * (h (x - t) - h x)) (g := fun t => K t * δ)
        (hKint.mul_const δ) (Eventually.of_forall fun t => ?_)
      · simpa [Real.norm_eq_abs] using this
      · by_cases ht : a < ‖t‖
        · have : K t = 0 := scaledUnitKernel_eq_zero_of_lt_norm ha ht
          simp [this]
        · have hdist : dist (x - t) x < η := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
            linarith [not_lt.mp ht]
          have := (hηh hdist)
          rw [Real.dist_eq] at this
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnn t)]
          exact mul_le_mul_of_nonneg_left this.le (hKnn t)
    _ = δ := by rw [integral_mul_const, hKone, one_mul]

/-- For `a ≤ 1` the mollification of a compactly supported function is supported
in the unit thickening of its support. -/
theorem support_wholeSpaceMollify_subset {h : Vec d → ℝ}
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Function.support (wholeSpaceMollify a h) ⊆
      Metric.cthickening 1 (tsupport h) := by
  intro x hx
  by_contra hxn
  apply hx
  simp only [wholeSpaceMollify, convolution_def]
  have : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ)
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a t) (h (x - t)) = 0 := by
    intro t
    by_cases ht : a < ‖t‖
    · simp [scaledUnitKernel_eq_zero_of_lt_norm ha ht]
    · have hmem : x - t ∉ tsupport h := fun hm =>
        hxn (Metric.mem_cthickening_of_dist_le x (x - t) 1 _ hm (by
          rw [dist_eq_norm, sub_sub_cancel]; linarith [not_lt.mp ht]))
      simp [image_eq_zero_of_notMem_tsupport hmem]
  simp [this]

private theorem wholeSpaceMollify_sub_eq {a : ℝ} (ha : 0 < a) {f h : Vec d → ℝ}
    (hf : LocallyIntegrable f volume) (hh : LocallyIntegrable h volume) :
    wholeSpaceMollify a f =
      wholeSpaceMollify a (f - h) + wholeSpaceMollify a h := by
  have e1 := convolutionExists_scaledUnitKernel ha (hf.sub hh)
  have e2 := convolutionExists_scaledUnitKernel ha hh
  have := e1.distrib_add e2
  simpa [wholeSpaceMollify] using this

/-- The whole-space mollification converges to any `L^p` function in `L^p`,
`1 ≤ p < ∞`, along the standard scale sequence. -/
theorem tendsto_eLpNorm_wholeSpaceMollify_sub {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpTop : p ≠ ∞) {f : Vec d → ℝ} (hf : MemLp f p volume) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (wholeSpaceMollify (a n) f - f) p volume) atTop
      (𝓝 0) := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεTop
  · exact Eventually.of_forall fun _ => le_top
  have hδ : ε / 3 ≠ 0 := (ENNReal.div_pos_iff.2 ⟨hε.ne', ENNReal.ofNat_ne_top⟩).ne'
  obtain ⟨h, hhc, hfh, hhcont, hhmem⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hpTop hδ
  set S := Metric.cthickening 1 (tsupport h) with hS
  have hSc : IsCompact S := hhc.isCompact.cthickening
  have hSvol : volume S ≠ ∞ := hSc.measure_lt_top.ne
  have hvolpow : volume S ^ (1 / p.toReal) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hSvol).ne
  -- choose the uniform tolerance
  have hpt : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpTop
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal c * volume S ^ (1 / p.toReal) ≤ ε / 3 := by
    set V := volume S ^ (1 / p.toReal)
    have hE : ε / 3 ≠ ∞ := ENNReal.div_ne_top hεTop (by norm_num)
    have hεpos : (0 : ℝ) < (ε / 3).toReal := ENNReal.toReal_pos hδ hE
    have hV : 0 ≤ V.toReal := ENNReal.toReal_nonneg
    refine ⟨(ε / 3).toReal / (V.toReal + 1), by positivity, ?_⟩
    calc ENNReal.ofReal ((ε / 3).toReal / (V.toReal + 1)) * V
        = ENNReal.ofReal ((ε / 3).toReal / (V.toReal + 1) * V.toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hvolpow]
      _ ≤ ENNReal.ofReal (ε / 3).toReal := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
      _ = ε / 3 := ENNReal.ofReal_toReal hE
  obtain ⟨a₀, ha₀, hclose⟩ := exists_forall_dist_wholeSpaceMollify_le hhcont hhc hc0
  filter_upwards [ha0.eventually (Iic_mem_nhds ha₀)] with n hn
  have hloc := hf.locallyIntegrable hp
  have hhloc : LocallyIntegrable h volume := hhcont.locallyIntegrable
  have h1 : eLpNorm (wholeSpaceMollify (a n) h - h) p volume ≤ ε / 3 := by
    refine le_trans ?_ hc
    refine eLpNorm_sub_le_of_dist_bdd volume hpTop hSc.measurableSet.nullMeasurableSet hc0.le ?_
      (fun x => hclose (a n) (ha n) hn x)
      (support_wholeSpaceMollify_subset (ha n) (ha1 n))
      (subset_tsupport h |>.trans (Metric.self_subset_cthickening _))
    exact ((contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) hp hpTop hhmem).1.continuous.sub
      hhcont).aestronglyMeasurable
  have h2 : eLpNorm (wholeSpaceMollify (a n) (f - h)) p volume ≤ ε / 3 := by
    refine (contDiff_memLp_convolution_scaledConvexApproxKernel hρ (ha n) hp hpTop
      (hf.sub hhmem)).2.2.trans ?_
    simpa using hfh
  have hdecomp : wholeSpaceMollify (a n) f - f =
      wholeSpaceMollify (a n) (f - h) + (wholeSpaceMollify (a n) h - h) +
        (h - f) := by
    rw [wholeSpaceMollify_sub_eq (ha n) hloc hhloc]; abel
  have h3 : eLpNorm (h - f) p volume ≤ ε / 3 := by
    rw [← eLpNorm_neg]; simpa using hfh
  rw [hdecomp]
  calc
    eLpNorm _ p volume ≤ eLpNorm (wholeSpaceMollify (a n) (f - h) +
        (wholeSpaceMollify (a n) h - h)) p volume + eLpNorm (h - f) p volume :=
      eLpNorm_add_le hp
    _ ≤ (eLpNorm (wholeSpaceMollify (a n) (f - h)) p volume +
        eLpNorm (wholeSpaceMollify (a n) h - h) p volume) + eLpNorm (h - f) p volume := by
      gcongr; exact eLpNorm_add_le hp
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := ENNReal.add_thirds ε

end PDE
