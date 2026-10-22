module

public import PDEFoundation.PDE.HarmonicConvolution
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify
public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Measure.LpPower

/-!
# Weak derivatives of whole-space mollifications and dilated cutoffs

Two ingredients for whole-space smooth density of `W^{1,p}(ℝ^d)`:

* the coordinate derivative of `K ⋆ u` is `K ⋆ g_i` when `g_i` is the weak
  derivative of `u` on the whole space;
* dilated smooth cutoffs `x ↦ B (R⁻¹ • x)`, with the `L^p` tail estimate that
  `(1 - cutoff) f → 0` as the dilation tends to infinity.
-/

@[expose] public section

open scoped ENNReal Convolution Topology

namespace PDE

open Filter MeasureTheory

variable {d : ℕ}

private theorem lsmul_flip_eq :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext; simp

/-- The coordinate derivative of a smooth-kernel convolution is the convolution
with the weak derivative. -/
theorem euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
    {K u g : Vec d → ℝ} (hK_supp : HasCompactSupport K)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hu : LocallyIntegrable u volume) {i : Fin d}
    (hweak : HasWeakPartialDerivOn Set.univ i u g) :
    euclideanCoordDeriv i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) =
      K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  rw [euclideanCoordDeriv_convolution_left hK_supp hK hu i]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => K (x - y)) :=
    hK.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y : Vec d => K (x - y)) :=
    hK_supp.comp_homeomorph (Homeomorph.subLeft x)
  have hw := hweak _ hφ hφc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hw
  have hderiv : ∀ y, (fderiv ℝ (fun y : Vec d => K (x - y)) y) (basisVec i) =
      -euclideanCoordDeriv i K (x - y) := fun y =>
    euclideanCoordDeriv_comp_const_sub hK x i y
  simp only [hderiv, mul_neg, integral_neg, neg_inj] at hw
  have hc : ∀ f h : Vec d → ℝ,
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h =
        h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := fun f h => by
    have := convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure (Vec d)))
      (f := f) (g := h)
    rw [lsmul_flip_eq] at this
    exact this.symm
  rw [hc (euclideanCoordDeriv i K) u, hc K g]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact hw

/-- The dilated unit cutoff. -/
noncomputable def wholeSpaceCutoff (R : ℝ) (x : Vec d) : ℝ :=
  (unitContDiffBump (d := d)) (R⁻¹ • x)

theorem contDiff_wholeSpaceCutoff (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (wholeSpaceCutoff (d := d) R) :=
  (unitContDiffBump (d := d)).contDiff (n := (⊤ : ℕ∞)) |>.comp
    (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => R⁻¹ • x)

theorem hasCompactSupport_wholeSpaceCutoff {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (wholeSpaceCutoff (d := d) R) := by
  exact (unitContDiffBump (d := d)).hasCompactSupport.comp_smul (inv_ne_zero hR.ne')

theorem wholeSpaceCutoff_nonneg (R : ℝ) (x : Vec d) : 0 ≤ wholeSpaceCutoff R x :=
  (unitContDiffBump (d := d)).nonneg

theorem wholeSpaceCutoff_le_one (R : ℝ) (x : Vec d) : wholeSpaceCutoff R x ≤ 1 :=
  (unitContDiffBump (d := d)).le_one

theorem wholeSpaceCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Vec d}
    (hx : ‖x‖ ≤ R / 2) : wholeSpaceCutoff R x = 1 := by
  apply (unitContDiffBump (d := d)).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
    Real.norm_of_nonneg hR.le]
  have : (unitContDiffBump (d := d)).rIn = 1 / 2 := rfl
  rw [this, ← div_eq_inv_mul, div_le_iff₀ hR]
  linarith

/-- Coordinate derivatives of the dilated cutoff are `O(1 / R)`. -/
theorem exists_abs_coord_deriv_wholeSpaceCutoff_le (i : Fin d) :
    ∃ M : ℝ, ∀ R : ℝ, 0 < R → ∀ x : Vec d,
      |euclideanCoordDeriv i (wholeSpaceCutoff R) x| ≤ M / R := by
  have hB : ContDiff ℝ (⊤ : ℕ∞) (unitContDiffBump (d := d)) :=
    (unitContDiffBump (d := d)).contDiff
  have hcont : Continuous (fun y : Vec d =>
      (fderiv ℝ (unitContDiffBump (d := d)) y) (basisVec i)) :=
    (hB.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun y : Vec d =>
      (fderiv ℝ (unitContDiffBump (d := d)) y) (basisVec i)) :=
    (unitContDiffBump (d := d)).hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨M, fun R hR x => ?_⟩
  have hfd : fderiv ℝ (wholeSpaceCutoff (d := d) R) x =
      (fderiv ℝ (unitContDiffBump (d := d)) (R⁻¹ • x)).comp (R⁻¹ • (ContinuousLinearMap.id ℝ (Vec d))) := by
    have h1 : HasFDerivAt (fun y : Vec d => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
      (hasFDerivAt_id x).const_smul R⁻¹
    exact ((hB.differentiable (by simp) _).hasFDerivAt.comp x h1).fderiv
  unfold euclideanCoordDeriv
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, abs_mul]
  rw [abs_of_pos (inv_pos.mpr hR), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using hM (R⁻¹ • x)) (inv_pos.mpr hR).le

/-- The `L^p` tail estimate for dilated cutoffs: `(cutoff_R - 1) f → 0`. -/
theorem tendsto_eLpNorm_wholeSpaceCutoff_sub_one_mul {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpTop : p ≠ ∞) {f : Vec d → ℝ} (hf : MemLp f p volume) {R : ℕ → ℝ}
    (hR : ∀ n, 0 < R n) (hRt : Tendsto R atTop atTop) :
    Tendsto (fun n => eLpNorm (fun x => (wholeSpaceCutoff (R n) x - 1) * f x) p volume)
      atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hfae := hf.aestronglyMeasurable
  have hbound_fin : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ≠ ∞ := by
    have := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hfae] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).mp this |>.ne
  have hlim : Tendsto
      (fun n => ∫⁻ x, ‖(wholeSpaceCutoff (R n) x - 1) * f x‖ₑ ^ p.toReal) atTop
      (𝓝 (∫⁻ _x : Vec d, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖f x‖ₑ ^ p.toReal)
      (fun n => ?_) (fun n => ?_) hbound_fin (Eventually.of_forall fun x => ?_)
    · exact (((contDiff_wholeSpaceCutoff (R n)).continuous.sub continuous_const).aestronglyMeasurable.mul
        hfae).enorm.pow_const _
    · refine Eventually.of_forall fun x => ?_
      apply ENNReal.rpow_le_rpow _ hq.le
      rw [enorm_mul]
      have h1 : ‖wholeSpaceCutoff (R n) x - 1‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr (wholeSpaceCutoff_le_one _ _))]
        exact ENNReal.ofReal_le_one.mpr (by linarith [wholeSpaceCutoff_nonneg (R n) x])
      calc _ ≤ 1 * ‖f x‖ₑ := by gcongr
        _ = _ := one_mul _
    · have : ∀ᶠ n in atTop, ‖(wholeSpaceCutoff (R n) x - 1) * f x‖ₑ ^ p.toReal = 0 := by
        filter_upwards [hRt.eventually_ge_atTop (2 * ‖x‖)] with n hn
        rw [wholeSpaceCutoff_eq_one (hR n) (by linarith)]
        simp [ENNReal.zero_rpow_of_pos hq]
      exact tendsto_const_nhds.congr' (this.mono fun n hn => hn.symm)
  simp only [lintegral_zero] at hlim
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hlim
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
  refine this.congr fun n => ?_
  simp only [Function.comp]
  have hm : AEStronglyMeasurable (fun x => (wholeSpaceCutoff (R n) x - 1) * f x) volume :=
    (((contDiff_wholeSpaceCutoff (R n)).continuous.sub continuous_const).aestronglyMeasurable.mul
        hfae)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hm]

end PDE
