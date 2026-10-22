module

public import PDEFoundation.Sobolev.Trace.Model.ExtAe
public import PDEFoundation.Sobolev.Trace.Model.ExtTranslate

/-!
# The extension converges to `g` at the boundary

`E g (·, τ) → g` in `L^p(Vec n)` as `τ → 0+` (approximate identity).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ}

theorem dilConv_sub_eq {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t)
    (x : Vec n) :
    dilConv n (extKernel n) g (x, t) - g x =
      ∫ y, dil n (extKernel n) (x - y) t * (g y - g x) := by
  have h1 := integrable_dil_mul n (isProfile_extKernel n) ht hg x
  have h2 : Integrable (fun y => dil n (extKernel n) (x - y) t * g x) volume :=
    (integrable_dil n (isProfile_extKernel n) ht x).mul_const _
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, integral_mul_const, integral_dil_sub n ht, extKernel_integral]
  have : ((t⁻¹) ^ n * (t ^ n * 1)) = 1 := by
    rw [mul_one, ← mul_pow, inv_mul_cancel₀ ht.ne', one_pow]
  rw [this, one_mul]
  rfl

theorem ofReal_abs_dilConv_sub_rpow_le {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ} (hgm : Measurable g)
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : Vec n) :
    ENNReal.ofReal (|dilConv n (extKernel n) g (x, t) - g x| ^ p) ≤
      ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) *
        ENNReal.ofReal (|g y - g x| ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have h1 : ENNReal.ofReal |dilConv n (extKernel n) g (x, t) - g x| ≤
      ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) t) * ENNReal.ofReal |g y - g x| := by
    rw [← Real.enorm_eq_ofReal_abs, dilConv_sub_eq hg ht x]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (dil_kernel_nonneg ht _),
      ENNReal.ofReal_mul (dil_kernel_nonneg ht _)]
  have hw : Measurable fun y => ENNReal.ofReal (dil n (extKernel n) (x - y) t) :=
    ENNReal.measurable_ofReal.comp (continuous_dil_sub n (isProfile_extKernel n) t x).measurable
  have hf : Measurable fun y => ENNReal.ofReal |g y - g x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hgm.sub_const _))
  have h2 := lintegral_mul_rpow_le volume hp hw.aemeasurable hf.aemeasurable
  rw [lintegral_ofReal_dil_sub ht x, ENNReal.one_rpow, one_mul] at h2
  calc ENNReal.ofReal (|dilConv n (extKernel n) g (x, t) - g x| ^ p)
      = ENNReal.ofReal |dilConv n (extKernel n) g (x, t) - g x| ^ p :=
        (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0).symm
    _ ≤ _ := ENNReal.rpow_le_rpow h1 hp0
    _ ≤ _ := h2
    _ = _ := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]

theorem tendsto_boundary_aux {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ} (hgm : Measurable g)
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun τ : ℝ => ∫⁻ x, ENNReal.ofReal (|dilConv n (extKernel n) g (x, τ) - g x| ^ p))
      (𝓝[>] 0) (𝓝 0) := by
  have hq : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp.le
  have hp0 : 0 ≤ p := by linarith
  have hloc := hg.locallyIntegrable hq
  have hT := tendsto_lintegral_translate (volume : Measure (Vec n)) hp.le hg
  rw [ENNReal.tendsto_nhds_zero] at hT ⊢
  intro ε hε
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.1 (hT ε hε)
  have hmem : Ioo (0 : ℝ) (min (1 / 2) η) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) hη0)
  filter_upwards [hmem] with τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hτη : τ < η := lt_of_lt_of_le hτ1 (min_le_right _ _)
  calc ∫⁻ x, ENNReal.ofReal (|dilConv n (extKernel n) g (x, τ) - g x| ^ p)
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (dil n (extKernel n) (x - y) τ) *
          ENNReal.ofReal (|g y - g x| ^ p) :=
        lintegral_mono fun x => ofReal_abs_dilConv_sub_rpow_le hp hgm hloc hτ0 x
    _ = ∫⁻ x, ∫⁻ w, ENNReal.ofReal (dil n (extKernel n) w τ) *
          ENNReal.ofReal (|g (x - w) - g x| ^ p) := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (dil n (extKernel n) (x - y) τ) *
          ENNReal.ofReal (|g y - g x| ^ p)) x]
        refine lintegral_congr fun w => ?_
        rw [sub_sub_cancel]
    _ = ∫⁻ w, ∫⁻ x, ENNReal.ofReal (dil n (extKernel n) w τ) *
          ENNReal.ofReal (|g (x - w) - g x| ^ p) := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
        · exact (continuous_dil n (isProfile_extKernel n) τ).measurable.comp measurable_snd
        · refine Measurable.pow_const ?_ p
          exact continuous_abs.measurable.comp
            ((hgm.comp (measurable_fst.sub measurable_snd)).sub (hgm.comp measurable_fst))
    _ ≤ ∫⁻ w, ENNReal.ofReal (dil n (extKernel n) w τ) * ε := by
        refine lintegral_mono fun w => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hd : dil n (extKernel n) w τ = 0
        · simp [hd]
        · refine mul_le_mul' le_rfl ?_
          have hw : vecEuclideanNorm w ≤ τ := by
            by_contra hlt
            exact hd (dil_eq_zero n (isProfile_extKernel n) hτ0 (not_le.1 hlt))
          have hwn : dist (-w) 0 < η := by
            rw [dist_zero_right, norm_neg]
            exact lt_of_le_of_lt ((norm_le_vecEuclideanNorm w).trans hw) hτη
          have := hη hwn
          simpa [sub_eq_add_neg] using this
    _ = ε := by
        have hmK : Measurable (fun w : Vec n => ENNReal.ofReal (dil n (extKernel n) w τ)) :=
          ENNReal.measurable_ofReal.comp (continuous_dil n (isProfile_extKernel n) τ).measurable
        rw [lintegral_mul_const ε hmK, lintegral_ofReal_dil hτ0, one_mul]

theorem modelExt_tendsto_boundary {p : ℝ} (hp : 1 < p) {g : Vec n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) :
    Tendsto (fun τ : ℝ => ∫⁻ x', ENNReal.ofReal (|modelExt n g (x', τ) - g x'| ^ p))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨g', hgm, hgg', hg'⟩ := memLp_ae_measurable_rep hg
  have h := tendsto_boundary_aux hp hgm hg'
  refine h.congr' ?_
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with τ hτ
  rw [modelExt_congr_ae hgg']
  refine lintegral_congr_ae (hgg'.mono fun x hx => ?_)
  beta_reduce
  rw [modelExt_eq_on_upperHalf g' (q := (x, τ)) hτ.1, extCutoff_eq_one hτ.2.le, one_mul, hx]

end PDE.TraceLane
