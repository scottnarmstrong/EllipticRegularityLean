module

public import PDEFoundation.Sobolev.Trace.Model.TraceCalculus
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Step 1 of the trace theorem: the `L^p` bound on the half-space

For `v` of class `C¹` up to the boundary with compact support,
`‖v(·, 0)‖_p^p ≤ p ‖v‖_p^{p-1} ‖∂ₜ v‖_p`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

/-- Tonelli on the open half-space. -/
theorem lintegral_upperHalf (F : Vec n × ℝ → ℝ≥0∞)
    (hF : AEMeasurable F (volume.restrict (upperHalf n))) :
    ∫⁻ z in upperHalf n, F z = ∫⁻ x', ∫⁻ t in Ioi (0 : ℝ), F (x', t) := by
  have h : (volume : Measure (Vec n × ℝ)).restrict (upperHalf n) =
      (volume.restrict (univ : Set (Vec n))).prod (volume.restrict (Ioi (0 : ℝ))) := by
    rw [upperHalf, Measure.volume_eq_prod, Measure.prod_restrict]
  rw [h] at hF ⊢
  rw [lintegral_prod _ hF, Measure.restrict_univ]

/-- Derivative of `|a|^p`: `|φ'(a)| = p |a|^(p-1)`. -/
theorem abs_deriv_norm_rpow {p : ℝ} (hp : 1 < p) (a : ℝ) :
    |deriv (fun x : ℝ => ‖x‖ ^ p) a| = p * |a| ^ (p - 1) := by
  rw [(hasDerivAt_norm_rpow a hp).deriv]
  have hp0 : 0 < p := by linarith
  by_cases ha : a = 0
  · subst ha
    simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have ha' : 0 < |a| := abs_pos.2 ha
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hp0, abs_of_nonneg (Real.rpow_nonneg ha'.le _),
      mul_assoc, ← Real.rpow_add_one ha'.ne']
    congr 2
    ring

theorem exists_height_zero {v : Vec n × ℝ → ℝ} (hK : ∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0)
    (x' : Vec n) : ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → v (x', t) = 0 := by
  obtain ⟨K, hKc, hKv⟩ := hK
  obtain ⟨M, hM⟩ := (hKc.image continuous_snd).bddAbove
  refine ⟨max M 0 + 1, by positivity, fun t ht => hKv _ (fun hmem => ?_)⟩
  have h1 : t ≤ M := hM ⟨_, hmem, rfl⟩
  have := le_max_left M 0
  linarith

/-- Pointwise (in `x'`) slice bound: `|v(x',0)|^p ≤ p ∫_0^∞ |v|^{p-1} |∂ₜ v| dt`. -/
theorem slice_pow_bound {p : ℝ} (hp : 1 < p) {v : Vec n × ℝ → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedUpperHalf n)) (hK : ∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0)
    (x' : Vec n) :
    ENNReal.ofReal (|v (x', 0)| ^ p) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal p *
        (ENNReal.ofReal (|v (x', t)| ^ (p - 1)) * ENNReal.ofReal |normDeriv v (x', t)|) := by
  obtain ⟨T, hT, hvT⟩ := exists_height_zero hK x'
  have hp0 : 0 < p := by linarith
  set φ : ℝ → ℝ := fun x => ‖x‖ ^ p with hφdef
  have hφ : ContDiff ℝ 1 φ := contDiff_norm_rpow hp
  set u : ℝ → ℝ := fun t => φ (v (x', t)) with hu
  set u' : ℝ → ℝ := fun t =>
    fderivWithin ℝ v (closedUpperHalf n) (x', t) (0, 1) * deriv φ (v (x', t)) with hu'
  have hsl := continuousOn_slice hv x'
  have hcu : ContinuousOn u (Icc 0 T) :=
    hφ.continuous.comp_continuousOn (hsl.mono Icc_subset_Ici_self)
  have hcu' : ContinuousOn u' (Icc 0 T) :=
    ((continuousOn_slice_deriv hv x').mono Icc_subset_Ici_self).mul
      ((hφ.continuous_deriv le_rfl).comp_continuousOn (hsl.mono Icc_subset_Ici_self))
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt u (u' t) t := by
    intro t ht
    have h1 := hasDerivAt_slice hv x' ht.1
    have h2 : HasDerivAt φ (deriv φ (v (x', t))) (v (x', t)) :=
      ((hφ.differentiable one_ne_zero) _).hasDerivAt
    have := h2.scomp t h1
    rw [smul_eq_mul, ← slice_deriv_eq (v := v) x' ht.1] at this
    exact this
  have hFTC := ofReal_abs_sub_le_lintegral hT.le hcu hd (hcu'.intervalIntegrable_of_Icc hT.le)
  have huT : u T = 0 := by
    simp only [hu, hφdef, hvT T le_rfl, norm_zero]
    exact Real.zero_rpow hp0.ne'
  have hu0 : |u T - u 0| = |v (x', 0)| ^ p := by
    rw [huT]
    simp only [hu, hφdef, zero_sub, abs_neg, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  rw [hu0] at hFTC
  refine hFTC.trans ?_
  calc ∫⁻ t in Ioc 0 T, ENNReal.ofReal |u' t|
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal |u' t| :=
        lintegral_mono_set Ioc_subset_Ioi_self
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        have ht0 : 0 < t := ht
        have h1 : |u' t| = p * |v (x', t)| ^ (p - 1) * |normDeriv v (x', t)| := by
          have hd1 : |deriv φ (v (x', t))| = p * |v (x', t)| ^ (p - 1) :=
            abs_deriv_norm_rpow hp _
          simp only [hu', abs_mul, slice_deriv_eq (v := v) x' ht0, hd1]
          ring
        rw [h1, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring

theorem measurable_normDeriv (v : Vec n × ℝ → ℝ) : Measurable (normDeriv v) :=
  measurable_fderiv_apply_const ℝ v ((0 : Vec n), (1 : ℝ))

theorem aemeasurable_upperHalf {v : Vec n × ℝ → ℝ} (hv : ContDiffOn ℝ 1 v (closedUpperHalf n)) :
    AEMeasurable v (volume.restrict (upperHalf n)) :=
  (hv.continuousOn.mono upperHalf_subset_closed).aemeasurable trace_measurableSet_upperHalf

/-- **Manuscript Step 1**: the `L^p` bound of the trace on the half-space. -/
theorem model_trace_Lp (n : ℕ) {p : ℝ} (hp : 1 < p) {v : Vec n × ℝ → ℝ}
    (hv : ContDiffOn ℝ 1 v (closedUpperHalf n)) (hK : ∃ K, IsCompact K ∧ ∀ z ∉ K, v z = 0) :
    ∫⁻ x', ENNReal.ofReal (|v (x', 0)| ^ p) ≤
      ENNReal.ofReal p * (∫⁻ z in upperHalf n, ENNReal.ofReal (|v z| ^ p)) ^ ((p - 1) / p) *
        (∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p)) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hpq : (Real.conjExponent p).HolderConjugate p :=
    (Real.HolderConjugate.conjExponent hp).symm
  set A : Vec n × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (|v z| ^ (p - 1)) with hA
  set B : Vec n × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal |normDeriv v z| with hB
  have hAae : AEMeasurable A (volume.restrict (upperHalf n)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable (aemeasurable_upperHalf hv)).pow_const _)
  have hBae : AEMeasurable B (volume.restrict (upperHalf n)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp (measurable_normDeriv v)).aemeasurable
  have h1 : ∫⁻ x', ENNReal.ofReal (|v (x', 0)| ^ p) ≤
      ∫⁻ x', ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal p * (A (x', t) * B (x', t)) :=
    lintegral_mono (fun x' => slice_pow_bound hp hv hK x')
  refine h1.trans ?_
  rw [← lintegral_upperHalf (fun z => ENNReal.ofReal p * (A z * B z)) ((hAae.mul hBae).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (upperHalf n)) hpq hAae hBae
  have hAp : ∫⁻ z in upperHalf n, A z ^ Real.conjExponent p =
      ∫⁻ z in upperHalf n, ENNReal.ofReal (|v z| ^ p) := by
    refine lintegral_congr (fun z => ?_)
    rw [hA]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (hpq.symm.symm.pos.le), ← Real.rpow_mul (abs_nonneg _)]
    congr 2
    have : (Real.conjExponent p) = p / (p - 1) := rfl
    rw [this]
    field_simp [(by linarith : p - 1 ≠ 0)]
  have hBp : ∫⁻ z in upperHalf n, B z ^ p =
      ∫⁻ z in upperHalf n, ENNReal.ofReal (|normDeriv v z| ^ p) := by
    refine lintegral_congr (fun z => ?_)
    simp only [hB]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
  have hexp : 1 / Real.conjExponent p = (p - 1) / p := by
    have : (Real.conjExponent p) = p / (p - 1) := rfl
    rw [this]
    field_simp
  rw [hAp, hBp, hexp] at hH
  rw [mul_assoc]
  exact mul_le_mul_right hH _

end PDE.TraceLane
