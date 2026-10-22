module

public import PDEFoundation.Sobolev.Inequalities.ConvexRieszKernel
public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Measure.RestrictedVolume

/-!
# The Riesz potential bound for smooth functions on convex domains

For a globally smooth function `u`, a bounded open convex set `V` of Euclidean diameter at most
`D`, and a measurable `S ⊆ V` of positive measure, the oscillation of `u` at a point `x ∈ V`
against the average over `S` is bounded by `D ^ d / (d |S|)` times the Riesz potential of
`|∇ u| 1_V` at `x`. The proof integrates the fundamental theorem of calculus along the segments
from `x` and collapses the segment parameter with the dilation change of variables.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

variable {d : ℕ}

private theorem segmentBlend_one_sub_eq (x y : Vec d) (s : ℝ) :
    segmentBlend x (1 - s) y = x + s • (y - x) := by
  ext i
  simp [segmentBlend, AffineMap.lineMap_apply_module]
  ring

/-- The pointwise oscillation of a smooth function against a point of `V` is bounded by the
`ℝ≥0∞` segment integral of the gradient along the segment to `x`. -/
theorem ofReal_abs_sub_le_lintegral_segment {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x y : Vec d} (hx : x ∈ V) (hy : y ∈ V) :
    ENNReal.ofReal |u x - u y| ≤
      ∫⁻ s in Ioc (0 : ℝ) 1,
        V.indicator (fun z => ENNReal.ofReal (vecEuclideanNorm (classicalGradient u z)))
            (x + s • (y - x)) * ENNReal.ofReal (vecEuclideanNorm (x - y)) := by
  have hgrad : Continuous fun z => vecEuclideanNorm (classicalGradient u z) :=
    continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient (hu.of_le (by norm_num) : ContDiff ℝ 1 u))
  have hseg : Continuous fun s : ℝ => x + s • (y - x) := by fun_prop
  have hF : Continuous fun s : ℝ =>
      vecEuclideanNorm (classicalGradient u (x + s • (y - x))) * vecEuclideanNorm (x - y) :=
    (hgrad.comp hseg).mul continuous_const
  have h1 := abs_sub_le_integral_euclideanGradient_mul_distance hu x y
  have h2 : ∫ t in (0 : ℝ)..1, vecEuclideanNorm (classicalGradient u (segmentBlend x t y)) *
        vecEuclideanNorm (x - y) =
      ∫ s in (0 : ℝ)..1, vecEuclideanNorm (classicalGradient u (x + s • (y - x))) *
        vecEuclideanNorm (x - y) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => vecEuclideanNorm (classicalGradient u (segmentBlend x t y)) *
        vecEuclideanNorm (x - y)) (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at this
    rw [← this]
    simp only [segmentBlend_one_sub_eq]
  rw [h2, intervalIntegral.integral_of_le zero_le_one] at h1
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ofReal_integral_eq_lintegral_ofReal
    (hF.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun s => mul_nonneg (vecEuclideanNorm_nonneg _)
      (vecEuclideanNorm_nonneg _))]
  refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
  have hmem : x + s • (y - x) ∈ V := by
    rw [← segmentBlend_one_sub_eq]
    exact segmentBlend_mem hV.convex hx hy (by linarith [hs.2]) (by linarith [hs.1])
  rw [indicator_of_mem hmem, ENNReal.ofReal_mul (vecEuclideanNorm_nonneg _)]

/-- The `ℝ≥0∞` form of the Riesz potential bound for a smooth function. -/
theorem ofReal_abs_sub_integralAverage_le_lintegral_riesz (hd : 0 < d) {V S : Set (Vec d)}
    {D : ℝ} (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hS : MeasurableSet S) (hSV : S ⊆ V)
    (hSpos : 0 < volume S) {x : Vec d} (hx : x ∈ V) :
    ENNReal.ofReal |u x - integralAverage S u| ≤
      ENNReal.ofReal (D ^ d / (d * (volume S).toReal)) *
        ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) *
          ENNReal.ofReal (vecEuclideanNorm (classicalGradient u y)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hSfin : volume S < ∞ := (hV.volume_lt_top).trans_le' (measure_mono hSV)
  have hSreal : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hSD : ∀ y ∈ S, vecEuclideanNorm (x - y) ≤ D := fun y hy => hVD hx (hSV hy)
  have hDpos : 0 < D := by
    rcases (le_trans (vecEuclideanNorm_nonneg (x - x)) (hVD hx hx)).eq_or_lt with h | h
    · exfalso
      have hsub : S ⊆ {x} := by
        intro y hy
        have := hSD y hy
        rw [← h] at this
        have h0 := (vecEuclideanNorm_eq_zero_iff (x := x - y)).1
          (le_antisymm this (vecEuclideanNorm_nonneg _))
        exact (sub_eq_zero.1 h0).symm
      exact hSpos.ne' (measure_mono_null hsub (measure_singleton x))
    · exact h
  have hcompact : IsCompact (closure V) := hV.isBoundedDomain.isBounded.isCompact_closure
  have hucont : Continuous u := hu.continuous
  have huS : IntegrableOn u S volume :=
    (hucont.continuousOn.integrableOn_compact hcompact).mono_set
      (hSV.trans subset_closure)
  have hint : IntegrableOn (fun y => u x - u y) S volume :=
    (integrableOn_const (C := u x) hSfin.ne).sub huS
  -- the real estimate
  have hreal : (volume S).toReal * |u x - integralAverage S u| ≤
      ∫ y in S, |u x - u y| := by
    have : (volume S).toReal * (u x - integralAverage S u) = ∫ y in S, (u x - u y) := by
      rw [integral_sub (integrableOn_const (C := u x) hSfin.ne) huS, setIntegral_const, integralAverage,
        smul_eq_mul, Measure.real, mul_sub, ← mul_assoc, mul_inv_cancel₀ hSreal.ne', one_mul]
    calc _ = |(volume S).toReal * (u x - integralAverage S u)| := by
          rw [abs_mul, abs_of_pos hSreal]
      _ = ‖∫ y in S, (u x - u y)‖ := by rw [this, Real.norm_eq_abs]
      _ ≤ _ := by simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict S) (fun y => u x - u y)
  have hgm : Measurable fun z => V.indicator
      (fun z => ENNReal.ofReal (vecEuclideanNorm (classicalGradient u z))) z :=
    (ENNReal.measurable_ofReal.comp (continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient
        (hu.of_le (by norm_num) : ContDiff ℝ 1 u))).measurable).indicator hV.measurableSet
  have hlin : ENNReal.ofReal (∫ y in S, |u x - u y|) =
      ∫⁻ y in S, ENNReal.ofReal |u x - u y| :=
    ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hkernel := lintegral_lintegral_segment_le_riesz hd hgm x hDpos hS hSD
  have hRHS : ∫⁻ z, ENNReal.ofReal (vecEuclideanNorm (x - z) ^ ((1 : ℝ) - d)) *
      V.indicator (fun z => ENNReal.ofReal (vecEuclideanNorm (classicalGradient u z))) z =
      ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) *
        ENNReal.ofReal (vecEuclideanNorm (classicalGradient u y)) := by
    rw [← lintegral_indicator hV.measurableSet]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ V <;> simp [Set.indicator, hz]
  have hmain : ENNReal.ofReal ((volume S).toReal * |u x - integralAverage S u|) ≤
      ENNReal.ofReal (D ^ d / d) *
        ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) *
          ENNReal.ofReal (vecEuclideanNorm (classicalGradient u y)) := by
    rw [← hRHS]
    refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
    rw [hlin]
    refine le_trans (lintegral_mono_ae ?_) hkernel
    exact (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy =>
      ofReal_abs_sub_le_lintegral_segment hV hu hx (hSV hy))
  have hfac : ENNReal.ofReal (D ^ d / (d * (volume S).toReal)) *
      ENNReal.ofReal ((volume S).toReal) = ENNReal.ofReal (D ^ d / d) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  rw [ENNReal.ofReal_mul hSreal.le, ← hfac, mul_assoc, mul_left_comm] at hmain
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hSreal) ENNReal.ofReal_ne_top).1 hmain

/-- For a smooth function the Riesz potential of `|∇ u| 1_V` is finite at every point of a
bounded convex domain of diameter at most `D`. -/
theorem lintegral_riesz_mul_gradient_lt_top (hd : 0 < d) {V : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {x : Vec d} (hx : x ∈ V) :
    ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) *
      ENNReal.ofReal (vecEuclideanNorm (classicalGradient u y)) < ∞ := by
  have hcompact : IsCompact (closure V) := hV.isBoundedDomain.isBounded.isCompact_closure
  have hgrad : Continuous fun z => vecEuclideanNorm (classicalGradient u z) :=
    continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient (hu.of_le (by norm_num) : ContDiff ℝ 1 u))
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hgrad.continuousOn
  have hsub : V ⊆ {y | vecEuclideanNorm (x - y) < D + 1} := by
    intro y hy
    have := hVD hx hy
    show vecEuclideanNorm (x - y) < D + 1
    linarith
  have hD0 : 0 ≤ D := le_trans (vecEuclideanNorm_nonneg _) (hVD hx hx)
  calc _ ≤ ∫⁻ y in V, ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) *
        ENNReal.ofReal M := by
        refine setLIntegral_mono' hV.measurableSet fun y hy => ?_
        gcongr
        have := hM y (subset_closure hy)
        rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] at this
        exact this
    _ = ENNReal.ofReal M * ∫⁻ y in V,
          ENNReal.ofReal (vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        exact lt_of_le_of_lt (lintegral_mono_set hsub)
          (lintegral_riesz_kernel_ball_lt_top hd x (by linarith))

/-- **Riesz potential bound on convex domains, smooth case.** For a globally smooth `u`, a bounded
open convex set `V` of Euclidean diameter at most `D`, a measurable `S ⊆ V` of positive measure
and every `x ∈ V`,
`|u x - (u)_S| ≤ D ^ d / (d |S|) ∫_V |x - y| ^ (1 - d) |∇ u y| dy`. -/
theorem abs_sub_integralAverage_le_riesz_of_contDiff (hd : 0 < d) {V S : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hS : MeasurableSet S) (hSV : S ⊆ V)
    (hSpos : 0 < volume S) {x : Vec d} (hx : x ∈ V) :
    |u x - integralAverage S u| ≤
      D ^ d / (d * (volume S).toReal) *
        ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
          vecEuclideanNorm (classicalGradient u y) := by
  have hfin := lintegral_riesz_mul_gradient_lt_top hd hV hVD hu hx
  have hmain := ofReal_abs_sub_integralAverage_le_lintegral_riesz hd hV hVD hu hS hSV hSpos hx
  have hnn : 0 ≤ᵐ[volume.restrict V] fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
      vecEuclideanNorm (classicalGradient u y) :=
    Filter.Eventually.of_forall fun y => mul_nonneg
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _) (vecEuclideanNorm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
      vecEuclideanNorm (classicalGradient u y)) (volume.restrict V) := by
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · exact (continuous_vecEuclideanNorm.comp
        (continuous_const.sub continuous_id)).measurable.pow_const _
    · exact (continuous_vecEuclideanNorm.comp
        (PDE.ContDiff.continuous_classicalGradient
          (hu.of_le (by norm_num) : ContDiff ℝ 1 u))).measurable
  have hint := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  simp only [ENNReal.ofReal_mul (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)] at hint
  rw [hint]
  have hSreal : 0 < (volume S).toReal := by
    have : volume S < ∞ := (hV.volume_lt_top).trans_le' (measure_mono hSV)
    exact ENNReal.toReal_pos hSpos.ne' this.ne
  have hC : 0 ≤ D ^ d / (d * (volume S).toReal) := by
    have hD0 : 0 ≤ D := le_trans (vecEuclideanNorm_nonneg _) (hVD hx hx)
    positivity
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hfin.ne]
  exact hmain

end PDE
