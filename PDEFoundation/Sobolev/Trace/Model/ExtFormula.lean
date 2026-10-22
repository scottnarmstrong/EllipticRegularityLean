module

public import PDEFoundation.Sobolev.Trace.Model.ExtDeriv

/-!
# `C¹` regularity and derivative formulas for the extension

On the open upper half-space `modelExt n g` is `C¹`; its tangential and normal derivatives are
the convolutions of `g` with the dilated profiles `extTan` and `extRad` (plus the cutoff term).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ}

theorem continuous_dilFDeriv_sub {t : ℝ} (ht : t ≠ 0) (x : Vec n) :
    Continuous fun y : Vec n => dilFDeriv n (x - y, t) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have h1 : ContinuousAt (fun y : Vec n => (x - y, t)) y :=
    (continuous_const.sub continuous_id).continuousAt.prodMk continuousAt_const
  exact ContinuousAt.comp (f := fun y : Vec n => (x - y, t)) (x := y)
    (continuousAt_dilFDeriv (n := n) (p := (x - y, t)) ht) h1

theorem integrable_fderivIntegrand {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {p : Vec n × ℝ} (hp : 0 < p.2) :
    Integrable (fun y => g y • dilFDeriv n (p.1 - y, p.2)) volume := by
  obtain ⟨bnd, hbi, hb⟩ := exists_dilFDeriv_bound hg hp
  refine hbi.mono' (hg.aestronglyMeasurable.smul (continuous_dilFDeriv_sub hp.ne' p.1).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun y => hb p (Metric.mem_ball_self (by positivity)) y

theorem continuousAt_fderivIntegral {g : Vec n → ℝ} (hg : LocallyIntegrable g volume)
    {p : Vec n × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : Vec n × ℝ => ∫ y, g y • dilFDeriv n (q.1 - y, q.2)) p := by
  obtain ⟨bnd, hbi, hb⟩ := exists_dilFDeriv_bound hg hp
  have hpos : ∀ᶠ q : Vec n × ℝ in 𝓝 p, 0 < q.2 :=
    continuous_snd.continuousAt.eventually (lt_mem_nhds hp)
  refine continuousAt_of_dominated (bound := bnd) ?_ ?_ hbi ?_
  · filter_upwards [hpos] with q hq
    exact hg.aestronglyMeasurable.smul (continuous_dilFDeriv_sub hq.ne' q.1).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds p (show 0 < p.2 / 2 by positivity)] with q hq
    exact Filter.Eventually.of_forall fun y => hb q hq y
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : ContinuousAt (fun q : Vec n × ℝ => (q.1 - y, q.2)) p :=
      (continuous_fst.sub continuous_const).continuousAt.prodMk continuous_snd.continuousAt
    exact (continuousAt_const : ContinuousAt (fun _ : Vec n × ℝ => g y) p).smul (ContinuousAt.comp (f := fun q : Vec n × ℝ => (q.1 - y, q.2))
      (x := p) (continuousAt_dilFDeriv (n := n) (p := (p.1 - y, p.2)) hp.ne') h1)

theorem isOpen_upperHalf (n : ℕ) : IsOpen (upperHalf n) :=
  isOpen_univ.prod isOpen_Ioi

theorem mem_upperHalf {n : ℕ} {p : Vec n × ℝ} : p ∈ upperHalf n ↔ 0 < p.2 := by
  simp [upperHalf]

theorem contDiffOn_extConv {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) :
    ContDiffOn ℝ 1 (dilConv n (extKernel n) g) (upperHalf n) := by
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
  rw [h1, contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_upperHalf n)]
  refine ⟨fun p hp => (hasFDerivAt_extConv hg (mem_upperHalf.1 hp)).differentiableAt
    |>.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
  rw [contDiffOn_zero]
  intro p hp
  have := continuousAt_fderivIntegral hg (mem_upperHalf.1 hp)
  refine ContinuousAt.continuousWithinAt ?_
  refine this.congr ?_
  filter_upwards [(isOpen_upperHalf n).mem_nhds hp] with q hq
  exact ((hasFDerivAt_extConv hg (mem_upperHalf.1 hq)).fderiv).symm

theorem modelExt_eq_on_upperHalf (g : Vec n → ℝ) {q : Vec n × ℝ} (hq : 0 < q.2) :
    modelExt n g q = extCutoff q.2 * dilConv n (extKernel n) g q := by
  simp [modelExt, hq]

theorem contDiffOn_modelExt {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) :
    ContDiffOn ℝ 1 (modelExt n g) (upperHalf n) := by
  have h1 : ContDiffOn ℝ 1 (fun q : Vec n × ℝ => extCutoff q.2 * dilConv n (extKernel n) g q)
      (upperHalf n) :=
    ((extCutoff_contDiff.comp contDiff_snd).contDiffOn).mul (contDiffOn_extConv hg)
  exact h1.congr fun q hq => modelExt_eq_on_upperHalf g (mem_upperHalf.1 hq)

theorem hasFDerivAt_modelExt {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) {p : Vec n × ℝ}
    (hp : 0 < p.2) :
    HasFDerivAt (modelExt n g)
      (extCutoff p.2 • (∫ y, g y • dilFDeriv n (p.1 - y, p.2)) +
        dilConv n (extKernel n) g p •
          (deriv extCutoff p.2 • ContinuousLinearMap.snd ℝ (Vec n) ℝ)) p := by
  have hχ : HasFDerivAt (fun q : Vec n × ℝ => extCutoff q.2)
      (deriv extCutoff p.2 • ContinuousLinearMap.snd ℝ (Vec n) ℝ) p :=
    (((extCutoff_contDiff.differentiable one_ne_zero) p.2).hasDerivAt).comp_hasFDerivAt p
      hasFDerivAt_snd
  have h := hχ.mul (hasFDerivAt_extConv hg hp)
  have hev : (fun q : Vec n × ℝ => extCutoff q.2 * dilConv n (extKernel n) g q) =ᶠ[𝓝 p]
      modelExt n g := by
    filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds hp)] with q hq
    exact (modelExt_eq_on_upperHalf g hq).symm
  refine (h.congr_of_eventuallyEq hev.symm).congr_fderiv ?_
  rw [add_comm]

theorem dilFDeriv_basis (n : ℕ) (z : Vec n) (t : ℝ) (i : Fin n) :
    dilFDeriv n (z, t) (basisVec i, 0) = dil (n + 1) (extTan n i) z t := by
  simp [dilFDeriv, dil, extTan]

theorem dilFDeriv_normal (n : ℕ) (z : Vec n) (t : ℝ) :
    dilFDeriv n (z, t) (0, 1) = dil (n + 1) (extRad n) z t := by
  simp [dilFDeriv, dil]

theorem tanGrad_modelExt {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) {z : Vec n × ℝ}
    (hz : 0 < z.2) (i : Fin n) :
    tanGrad (modelExt n g) z i = extCutoff z.2 * dilConv (n + 1) (extTan n i) g z := by
  unfold tanGrad
  rw [(hasFDerivAt_modelExt hg hz).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, add_zero]
  rw [ContinuousLinearMap.integral_apply (integrable_fderivIntegrand hg hz)]
  unfold dilConv
  simp_rw [smul_apply, dilFDeriv_basis, smul_eq_mul, mul_comm (g _)]

theorem normDeriv_modelExt {g : Vec n → ℝ} (hg : LocallyIntegrable g volume) {z : Vec n × ℝ}
    (hz : 0 < z.2) :
    normDeriv (modelExt n g) z = extCutoff z.2 * dilConv (n + 1) (extRad n) g z +
      deriv extCutoff z.2 * dilConv n (extKernel n) g z := by
  unfold normDeriv
  rw [(hasFDerivAt_modelExt hg hz).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one]
  rw [ContinuousLinearMap.integral_apply (integrable_fderivIntegrand hg hz)]
  unfold dilConv
  simp_rw [smul_apply, dilFDeriv_normal, smul_eq_mul, mul_comm (g _)]
  ring

end PDE.TraceLane
