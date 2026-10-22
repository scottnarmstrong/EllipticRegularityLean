module

public import PDEFoundation.Sobolev.Inequalities.ConvexRieszOperator
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Measure.EuclideanVectorIntegral

/-!
# The Riesz potential bound on convex domains

This file proves the Riesz potential bound (Gilbarg--Trudinger, Lemma 7.16) for
`W^{1,1}` functions on a bounded open convex domain of Euclidean diameter at most `D`:
for a measurable `S ⊆ V` of positive measure and almost every `x ∈ V`,
`|u x - (u)_S| ≤ D ^ d / (d |S|) ∫_V |x - y| ^ (1 - d) |∇ u y| dy`.

The smooth case is `abs_sub_integralAverage_le_riesz_of_contDiff`. The general case passes to
the limit along the smooth convex approximation of `W^{1,1}`; the Riesz potential is a bounded
operator on `L¹(V)` by Tonelli, and an almost everywhere convergent subsequence is extracted
with a summability argument.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

variable {d : ℕ}

/-- Averages over a subset of a bounded domain converge when the functions converge in `L¹`. -/
theorem tendsto_integralAverage_of_tendsto_lintegral {V S : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hSV : S ⊆ V)
    (hSpos : 0 < volume S) {f : ℕ → Vec d → ℝ} {f₀ : Vec d → ℝ}
    (hf : ∀ n, IntegrableOn (f n) V) (hf₀ : IntegrableOn f₀ V)
    (hlim : Tendsto (fun n => ∫⁻ y in V, ENNReal.ofReal |f n y - f₀ y|) atTop (𝓝 0)) :
    Tendsto (fun n => integralAverage S (f n)) atTop (𝓝 (integralAverage S f₀)) := by
  have hSfin : volume S < ∞ := (hV.volume_lt_top).trans_le' (measure_mono hSV)
  have hSreal : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hbound : ∀ n, |integralAverage S (f n) - integralAverage S f₀| ≤
      (volume S).toReal⁻¹ * (∫⁻ y in V, ENNReal.ofReal |f n y - f₀ y|).toReal := by
    intro n
    have hint : IntegrableOn (fun y => |f n y - f₀ y|) V := ((hf n).sub hf₀).abs
    have h1 : integralAverage S (f n) - integralAverage S f₀ =
        (volume S).toReal⁻¹ * ∫ y in S, (f n y - f₀ y) := by
      unfold integralAverage
      rw [← mul_sub, integral_sub ((hf n).mono_set hSV) (hf₀.mono_set hSV)]
    have h2 : ∫ y in V, |f n y - f₀ y| =
        (∫⁻ y in V, ENNReal.ofReal |f n y - f₀ y|).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
        hint.aestronglyMeasurable
    rw [h1, abs_mul, abs_of_pos (inv_pos.2 hSreal), ← h2]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hSreal.le)
    calc |∫ y in S, (f n y - f₀ y)| ≤ ∫ y in S, |f n y - f₀ y| := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := volume.restrict S) (fun y => f n y - f₀ y)
      _ ≤ ∫ y in V, |f n y - f₀ y| :=
          setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => abs_nonneg _)
            hSV.eventuallyLE
  have hzero : Tendsto (fun n => (volume S).toReal⁻¹ *
      (∫⁻ y in V, ENNReal.ofReal |f n y - f₀ y|).toReal) atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).const_mul
      (volume S).toReal⁻¹
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [Real.dist_eq] using hbound n) hzero

/-- A sequence of nonnegative functions with integrals tending to zero has a subsequence
tending to zero almost everywhere. -/
theorem exists_strictMono_ae_tendsto_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : ℕ → α → ℝ≥0∞} (hE : ∀ n, AEMeasurable (E n) μ)
    (hlim : Tendsto (fun n => ∫⁻ x, E n x ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂μ, Tendsto (fun k => E (φ k) x) atTop (𝓝 0) := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, ∫⁻ x, E n x ∂μ ≤ (1 / 2 : ℝ≥0∞) ^ k := fun k =>
    hlim.eventually (ge_mem_nhds (ENNReal.pow_pos (by simp) k))
  obtain ⟨φ, hφ, hφle⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∫⁻ x, ∑' k, E (φ k) x ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => hE (φ k)]
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ k) ?_ (ENNReal.tsum_le_tsum hφle)
    rw [ENNReal.tsum_geometric]
    simp
  have hae : ∀ᵐ x ∂μ, ∑' k, E (φ k) x < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun k => hE (φ k)) hsum
  filter_upwards [hae] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

theorem tendsto_of_tendsto_ofReal_abs_sub {a : ℕ → ℝ} {b : ℝ}
    (h : Tendsto (fun k => ENNReal.ofReal |a k - b|) atTop (𝓝 0)) : Tendsto a atTop (𝓝 b) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at this
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using this

private theorem aemeasurable_vecEuclideanNorm_grad {V : Set (Vec d)} (u : W1pFunction V 1) :
    AEMeasurable (fun y => vecEuclideanNorm (u.grad y)) (volumeOn V) :=
  continuous_vecEuclideanNorm.measurable.comp_aemeasurable
    (aemeasurable_pi_iff.2 fun i => (u.grad_memLp i).aestronglyMeasurable.aemeasurable)

/-- The `ℝ≥0∞` form of the Riesz potential bound for `W^{1,1}` functions on a convex domain. -/
theorem ofReal_abs_sub_integralAverage_ae_le_lintegralRieszOn (hd : 0 < d) {V S : Set (Vec d)}
    {D : ℝ} (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D)
    (u : W1pFunction V 1) (hS : MeasurableSet S) (hSV : S ⊆ V) (hSpos : 0 < volume S) :
    ∀ᵐ x ∂volumeOn V, ENNReal.ofReal |u.toFun x - integralAverage S u.toFun| ≤
      ENNReal.ofReal (D ^ d / (d * (volume S).toReal)) *
        lintegralRieszOn V (fun y => ENNReal.ofReal (vecEuclideanNorm (u.grad y))) x := by
  have := hV.isFiniteMeasure_volumeOn
  obtain ⟨x1, hx1⟩ := nonempty_of_measure_ne_zero hSpos.ne'
  have hD : 0 ≤ D := le_trans (vecEuclideanNorm_nonneg _) (hVD (hSV hx1) (hSV hx1))
  have := hV.isFiniteMeasure_volumeOn
  obtain ⟨x0, r, hr, hball⟩ :=
    exists_metricClosedBall_subset_of_isOpenBoundedConvexDomain hV ⟨x1, hSV hx1⟩
  let ψ : ℕ → W1pFunction V 1 := fun n =>
    W1pFunction.convexApproxSmoothW1p hV (le_refl (1 : ℝ≥0∞)) u x0 hr n
  have hψsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n).toFun := fun n =>
    W1pFunction.contDiff_convexApproxSmoothW1p_toFun hV (le_refl (1 : ℝ≥0∞)) u x0 hr n
  let g : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (vecEuclideanNorm (u.grad y))
  let e : ℕ → Vec d → ℝ≥0∞ := fun n y =>
    ENNReal.ofReal (vecEuclideanNorm ((ψ n).grad y - u.grad y))
  let c : ℕ → Vec d → ℝ≥0∞ := fun n y => ENNReal.ofReal |(ψ n).toFun y - u.toFun y|
  have hgm : AEMeasurable g (volumeOn V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_vecEuclideanNorm_grad u)
  have hefm : ∀ n, AEMeasurable
      (fun y => vecEuclideanNorm ((ψ n).grad y - u.grad y)) (volumeOn V) := fun n =>
    continuous_vecEuclideanNorm.measurable.comp_aemeasurable
      ((aemeasurable_pi_iff.2 fun i => ((ψ n).grad_memLp i).aestronglyMeasurable.aemeasurable).sub
        (aemeasurable_pi_iff.2 fun i => (u.grad_memLp i).aestronglyMeasurable.aemeasurable))
  have hcfm : ∀ n, AEMeasurable (fun y => (ψ n).toFun y - u.toFun y) (volumeOn V) := fun n =>
    (ψ n).memLp.aestronglyMeasurable.aemeasurable.sub u.memLp.aestronglyMeasurable.aemeasurable
  have hem : ∀ n, AEMeasurable (e n) (volumeOn V) := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hefm n)
  have hcm : ∀ n, AEMeasurable (c n) (volumeOn V) := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
      (hcfm n))
  have hb : Tendsto (fun n => ∫⁻ y in V, e n y) atTop (𝓝 0) := by
    have := W1pFunction.tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub hV
      (le_refl (1 : ℝ≥0∞)) ENNReal.one_ne_top u hball hr
    refine this.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm (hefm n).aestronglyMeasurable]
    refine lintegral_congr fun y => ?_
    simp only [e, Real.enorm_eq_ofReal_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]
  have hcl : Tendsto (fun n => ∫⁻ y in V, c n y) atTop (𝓝 0) := by
    have := W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hV
      (le_refl (1 : ℝ≥0∞)) ENNReal.one_ne_top u hball hr
    refine this.congr fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm (hcfm n).aestronglyMeasurable]
    refine lintegral_congr fun y => ?_
    simp only [c, Real.enorm_eq_ofReal_abs]
  have hCtop := lintegral_riesz_kernel_euclideanBall_lt_top hd (R := D + 1) (by linarith)
  have hLe : ∀ n, ∫⁻ x in V, lintegralRieszOn V (e n) x ≤
      (∫⁻ z in euclideanBall (0 : Vec d) (D + 1),
        ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d))) * ∫⁻ y in V, e n y := fun n =>
    lintegral_lintegralRieszOn_le hV hVD hD (hem n)
  generalize (∫⁻ z in euclideanBall (0 : Vec d) (D + 1),
        ENNReal.ofReal (vecEuclideanNorm z ^ ((1 : ℝ) - d))) = C at hCtop hLe
  let E : ℕ → Vec d → ℝ≥0∞ := fun n x => lintegralRieszOn V (e n) x + c n x
  have hEm : ∀ n, AEMeasurable (E n) (volumeOn V) := fun n =>
    (measurable_lintegralRieszOn V (hem n)).aemeasurable.add (hcm n)
  have haE : Tendsto (fun n => ∫⁻ x in V, E n x) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => C * (∫⁻ y in V, e n y) + ∫⁻ y in V, c n y) atTop (𝓝 0) := by
      have := (ENNReal.Tendsto.const_mul hb (Or.inr hCtop.ne)).add hcl
      rwa [mul_zero, zero_add] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => bot_le) fun n => ?_
    calc ∫⁻ x in V, E n x = (∫⁻ x in V, lintegralRieszOn V (e n) x) + ∫⁻ x in V, c n x :=
          lintegral_add_left (measurable_lintegralRieszOn V (hem n)) _
      _ ≤ _ := add_le_add (hLe n) le_rfl
  obtain ⟨φ, hφ, hae⟩ := exists_strictMono_ae_tendsto_zero hEm haE
  have havg : Tendsto (fun k => integralAverage S (ψ (φ k)).toFun) atTop
      (𝓝 (integralAverage S u.toFun)) := by
    refine (tendsto_integralAverage_of_tendsto_lintegral (f := fun n => (ψ n).toFun) hV hSV hSpos
      (fun n => (ψ n).memLp.integrable le_rfl) (u.memLp.integrable le_rfl) ?_).comp
      hφ.tendsto_atTop
    exact hcl
  filter_upwards [hae, ae_restrict_mem hV.measurableSet] with x hx hxV
  have hE1 : Tendsto (fun k => lintegralRieszOn V (e (φ k)) x) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx (fun k => bot_le)
      fun k => le_self_add
  have hE2 : Tendsto (fun k => c (φ k) x) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hx (fun k => bot_le)
      fun k => le_add_self
  have hxlim : Tendsto (fun k => (ψ (φ k)).toFun x) atTop (𝓝 (u.toFun x)) :=
    tendsto_of_tendsto_ofReal_abs_sub hE2
  have hleft : Tendsto (fun k => ENNReal.ofReal |(ψ (φ k)).toFun x - integralAverage S (ψ (φ k)).toFun|)
      atTop (𝓝 (ENNReal.ofReal |u.toFun x - integralAverage S u.toFun|)) :=
    (ENNReal.tendsto_ofReal (hxlim.sub havg).abs)
  have hright : Tendsto (fun k => ENNReal.ofReal (D ^ d / (d * (volume S).toReal)) *
      (lintegralRieszOn V g x + lintegralRieszOn V (e (φ k)) x)) atTop
      (𝓝 (ENNReal.ofReal (D ^ d / (d * (volume S).toReal)) * lintegralRieszOn V g x)) := by
    have := ENNReal.Tendsto.const_mul (tendsto_const_nhds (x := lintegralRieszOn V g x)|>.add hE1)
      (Or.inr (ENNReal.ofReal_ne_top (r := D ^ d / (d * (volume S).toReal))))
    simpa using this
  refine le_of_tendsto_of_tendsto' hleft hright fun k => ?_
  refine (ofReal_abs_sub_integralAverage_le_lintegral_riesz hd hV hVD (hψsmooth (φ k)) hS hSV
    hSpos hxV).trans ?_
  refine mul_le_mul' le_rfl ?_
  calc lintegralRieszOn V (fun y => ENNReal.ofReal (vecEuclideanNorm ((ψ (φ k)).grad y))) x
      ≤ lintegralRieszOn V (fun y => g y + e (φ k) y) x := by
        refine lintegral_mono fun y => mul_le_mul' le_rfl ?_
        have h1 : vecEuclideanNorm ((ψ (φ k)).grad y) ≤
            vecEuclideanNorm (u.grad y) + vecEuclideanNorm ((ψ (φ k)).grad y - u.grad y) := by
          have := vecEuclideanNorm_add_le (u.grad y) ((ψ (φ k)).grad y - u.grad y)
          simpa using this
        exact (ENNReal.ofReal_le_ofReal h1).trans
          (ENNReal.ofReal_add_le)
    _ = _ := lintegralRieszOn_add hgm x

/-- The `d = 0` case of the Riesz potential bound: the ambient space is a point. -/
private theorem abs_sub_integralAverage_ae_le_riesz_zero {V S : Set (Vec 0)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (u : W1pFunction V 1) (hSV : S ⊆ V) (hSpos : 0 < volume S) :
    ∀ᵐ x ∂volumeOn V, |u.toFun x - integralAverage S u.toFun| ≤
      D ^ 0 / ((0 : ℕ) * (volume S).toReal) *
        ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - (0 : ℕ)) *
          vecEuclideanNorm (u.grad y) := by
  refine Filter.Eventually.of_forall fun x => ?_
  have hSfin : volume S < ∞ := (hV.volume_lt_top).trans_le' (measure_mono hSV)
  have hSreal : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  obtain ⟨x1, hx1⟩ := nonempty_of_measure_ne_zero hSpos.ne'
  have hxeq : ∀ y : Vec 0, u.toFun y = u.toFun x := fun y => congrArg _ (Subsingleton.elim y x)
  have havg : integralAverage S u.toFun = u.toFun x := by
    unfold integralAverage
    simp only [hxeq, integral_const, smul_eq_mul, Measure.real, MeasurableSet.univ,
      Measure.restrict_apply, Set.univ_inter]
    field_simp
  simp [havg]

/-- **Riesz potential bound on convex domains** (Gilbarg--Trudinger, Lemma 7.16). For a bounded
open convex `V` of Euclidean diameter at most `D`, `u ∈ W^{1,1}(V)` and a measurable `S ⊆ V` of
positive measure, for almost every `x ∈ V`,
`|u x - (u)_S| ≤ D ^ d / (d |S|) ∫_V |x - y| ^ (1 - d) |∇ u y| dy`. -/
theorem abs_sub_integralAverage_ae_le_riesz {V S : Set (Vec d)} {D : ℝ}
    (hV : IsOpenBoundedConvexDomain V) (hVD : HasEuclideanDiameterLE V D)
    (u : W1pFunction V 1) (hS : MeasurableSet S) (hSV : S ⊆ V) (hSpos : 0 < volume S) :
    ∀ᵐ x ∂volumeOn V, |u.toFun x - integralAverage S u.toFun| ≤
      D ^ d / (d * (volume S).toReal) *
        ∫ y in V, vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) * vecEuclideanNorm (u.grad y) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact abs_sub_integralAverage_ae_le_riesz_zero hV u hSV hSpos
  have := hV.isFiniteMeasure_volumeOn
  obtain ⟨x1, hx1⟩ := nonempty_of_measure_ne_zero hSpos.ne'
  have hD : 0 ≤ D := le_trans (vecEuclideanNorm_nonneg _) (hVD (hSV hx1) (hSV hx1))
  have hSfin : volume S < ∞ := (hV.volume_lt_top).trans_le' (measure_mono hSV)
  have hSreal : 0 < (volume S).toReal := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hC : 0 ≤ D ^ d / (d * (volume S).toReal) := by positivity
  have hmain := ofReal_abs_sub_integralAverage_ae_le_lintegralRieszOn hd hV hVD u hS hSV hSpos
  have hgint : Integrable (fun y => vecEuclideanNorm (u.grad y)) (volumeOn V) :=
    integrable_vecEuclideanNorm_of_coord u.grad fun i => (u.grad_memLp i).integrable le_rfl
  have hgm : AEMeasurable (fun y => ENNReal.ofReal (vecEuclideanNorm (u.grad y))) (volumeOn V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_vecEuclideanNorm_grad u)
  have hCtop := lintegral_riesz_kernel_euclideanBall_lt_top hd (R := D + 1) (by linarith)
  have hfin : ∀ᵐ x ∂volumeOn V, lintegralRieszOn V
      (fun y => ENNReal.ofReal (vecEuclideanNorm (u.grad y))) x < ∞ := by
    refine ae_lt_top' (measurable_lintegralRieszOn V hgm).aemeasurable ?_
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hCtop.ne hgint.lintegral_lt_top.ne) ?_
    exact lintegral_lintegralRieszOn_le hV hVD hD hgm
  filter_upwards [hmain, hfin] with x hx hxfin
  have hnn : 0 ≤ᵐ[volume.restrict V] fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
      vecEuclideanNorm (u.grad y) :=
    Filter.Eventually.of_forall fun y => mul_nonneg
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _) (vecEuclideanNorm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun y => vecEuclideanNorm (x - y) ^ ((1 : ℝ) - d) *
      vecEuclideanNorm (u.grad y)) (volume.restrict V) :=
    (((continuous_vecEuclideanNorm.comp
      (continuous_const.sub continuous_id)).measurable.pow_const _).aemeasurable.mul
      (aemeasurable_vecEuclideanNorm_grad u)).aestronglyMeasurable
  have hint := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  simp only [ENNReal.ofReal_mul (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _)] at hint
  change ∫ y in V, _ = (lintegralRieszOn V _ x).toReal at hint
  rw [hint, ← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul hC,
    ENNReal.ofReal_toReal hxfin.ne]
  exact hx

end PDE
