module

public import EllipticRegularity.Parabolic.Energy.Bounds

/-!
# Fubini step: the space-time form of the mollified energy identity
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

/-- The space-time measure on `K × (s,t]`. -/
noncomputable abbrev μP : Measure (Vec d × ℝ) := volume.restrict (D.K ×ˢ Ioc D.s D.t)

theorem μP_eq : D.μP = (volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t)) :=
  volume_restrict_prod _ _

instance : IsFiniteMeasure D.μP :=
  ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top D.hK.measure_lt_top (by simp)⟩

instance : IsFiniteMeasure (volume.restrict D.K) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact D.hK.measure_lt_top⟩

theorem phi_continuous : Continuous D.φ := D.hφ.continuous

theorem parTimeDeriv_continuous : Continuous (parTimeDeriv D.φ) :=
  (D.hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem parSpaceGrad_continuous (i : Fin d) : Continuous fun z => parSpaceGrad D.φ z i :=
  (D.hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem bound_on_slab {f : Vec d × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, ∀ z ∈ D.K ×ˢ Icc D.s D.t, |f z| ≤ M := by
  obtain ⟨M, hM⟩ := (D.hK.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun z hz => by simpa using hM z hz⟩

theorem ae_bound_on_slab {f : Vec d × ℝ → ℝ} (hf : Continuous f) :
    ∃ M : ℝ, ∀ᵐ z ∂D.μP, |f z| ≤ M := by
  obtain ⟨M, hM⟩ := D.bound_on_slab hf
  refine ⟨M, ?_⟩
  exact (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Filter.Eventually.of_forall fun z hz => hM z ⟨hz.1, Ioc_subset_Icc_self hz.2⟩)

theorem stronglyMeasurable_Dh (a : ℝ) :
    StronglyMeasurable fun z : Vec d × ℝ => D.Dh a z.1 z.2 := by
  have hF : Measurable fun p : (Vec d × ℝ) × Vec d =>
      ∑ i, D.G (p.2, p.1.2) i * fderiv ℝ (kern a) (p.1.1 - p.2) (basisVec i) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.mul ?_ ?_
    · exact (D.hGm i).comp (measurable_snd.prodMk measurable_fst.snd)
    · exact (kern_fderiv_continuous a (basisVec i)).measurable.comp
        (measurable_fst.fst.sub measurable_snd)
  have := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict D.K1)
  exact this

theorem v_aestronglyMeasurable (a : ℝ) : AEStronglyMeasurable (D.v a) D.μP :=
  aestronglyMeasurable_mollT D.K1_measurable D.K D.hu2.aestronglyMeasurable a

theorem ae_v_bound {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    ∃ B : ℝ, ∀ᵐ z ∂D.μP, |D.v a z| ≤ B := by
  obtain ⟨B, hB⟩ := D.exists_v_bound ha haδ
  exact ⟨B, (ae_restrict_iff' (D.K_measurable.prod measurableSet_Ioc)).2
    (Filter.Eventually.of_forall fun z hz => hB z.1 hz.1 z.2 ⟨hz.2.1.le, hz.2.2⟩)⟩

/-- First integrand: `φ ∂ₜφ v²`. -/
noncomputable def H1 (a : ℝ) (z : Vec d × ℝ) : ℝ := D.φ z * parTimeDeriv D.φ z * D.v a z ^ 2

/-- Second integrand: `φ² v D̂`. -/
noncomputable def H2 (a : ℝ) (z : Vec d × ℝ) : ℝ := D.φ z ^ 2 * D.v a z * D.Dh a z.1 z.2

theorem H1_integrable {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) : Integrable (D.H1 a) D.μP := by
  obtain ⟨B, hB⟩ := D.ae_v_bound ha haδ
  obtain ⟨M, hM⟩ := D.ae_bound_on_slab (D.phi_continuous.mul D.parTimeDeriv_continuous)
  refine Integrable.of_bound (C := M * B ^ 2) ?_ ?_
  · exact ((D.phi_continuous.mul D.parTimeDeriv_continuous).aestronglyMeasurable).mul
      ((D.v_aestronglyMeasurable a).pow 2)
  · filter_upwards [hB, hM] with z hz1 hz2
    rw [Real.norm_eq_abs]
    unfold H1
    rw [abs_mul, abs_pow]
    have h0 : 0 ≤ |D.v a z| := abs_nonneg _
    exact mul_le_mul hz2 (pow_le_pow_left₀ h0 hz1 2) (by positivity) ((abs_nonneg _).trans hz2)

theorem H2_integrable {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) : Integrable (D.H2 a) D.μP := by
  obtain ⟨B, hB⟩ := D.ae_v_bound ha haδ
  obtain ⟨M, hM⟩ := D.ae_bound_on_slab (D.phi_continuous.pow 2)
  obtain ⟨C1, hC1, hDh⟩ := D.exists_Dh_le ha
  have hDh' : ∀ᵐ z ∂((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t))),
      |D.Dh a z.1 z.2| ≤ C1 * D.gG z.2 :=
    ae_prod_of_ae_slice (P := fun x σ => |D.Dh a x σ| ≤ C1 * D.gG σ) (by
      filter_upwards [hDh] with σ hσ x using hσ x)
  have hint : Integrable (fun z : Vec d × ℝ => (M * B * C1) * D.gG z.2) D.μP := by
    rw [μP_eq]
    exact (integrable_const (M * B * C1)).mul_prod D.gG_integrableOn
  refine hint.mono' ?_ ?_
  · exact (((D.phi_continuous.pow 2).aestronglyMeasurable).mul (D.v_aestronglyMeasurable a)).mul
      ((D.stronglyMeasurable_Dh a).aestronglyMeasurable)
  · have hDh'' : ∀ᵐ z ∂D.μP, |D.Dh a z.1 z.2| ≤ C1 * D.gG z.2 := by
      rw [μP_eq]; exact hDh'
    filter_upwards [hB, hM, hDh''] with z hz1 hz2 hz3
    rw [Real.norm_eq_abs]
    unfold H2
    rw [abs_mul, abs_mul, abs_pow]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hz2
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hz1
    have h1 : |D.φ z| ^ 2 ≤ M := by rw [← abs_pow]; exact hz2
    calc |D.φ z| ^ 2 * |D.v a z| * |D.Dh a z.1 z.2|
        ≤ M * B * (C1 * D.gG z.2) :=
          mul_le_mul (mul_le_mul h1 hz1 (abs_nonneg _) hM0) hz3 (abs_nonneg _) (by positivity)
      _ = M * B * C1 * D.gG z.2 := by ring

theorem slice_memLp {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    MemLp (D.K1.indicator fun y => D.u (y, τ)) 2 volume :=
  (memLp_indicator_iff_restrict D.K1_measurable).2 (D.hus τ hτ)

theorem v_contDiff {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => D.v a (x, τ) :=
  moll_contDiff ha ((D.slice_memLp hτ).locallyIntegrable (by norm_num))

theorem energy_integrableOn {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : τ ∈ Icc D.s D.t) :
    IntegrableOn (fun x => D.φ (x, τ) ^ 2 * D.v a (x, τ) ^ 2) D.K := by
  have h1 : Continuous fun x => D.φ (x, τ) := D.phi_continuous.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun x => D.v a (x, τ) := (D.v_contDiff ha hτ).continuous
  exact ((h1.pow 2).mul (h2.pow 2)).continuousOn.integrableOn_compact D.hK

theorem energy_spacetime {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) :
    (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2) =
      (∫ z, D.H1 a z ∂D.μP) + ∫ z, D.H2 a z ∂D.μP := by
  have ht : D.t ∈ Icc D.s D.t := ⟨D.hst.le, le_rfl⟩
  have hs : D.s ∈ Icc D.s D.t := ⟨le_rfl, D.hst.le⟩
  have hI1 := D.energy_integrableOn ha ht
  have hI2 := D.energy_integrableOn ha hs
  have hlhs : (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (∫ x in D.K, D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2) =
      ∫ x in D.K, ((1 / 2 : ℝ) * (D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2)) := by
    rw [integral_sub (hI1.const_mul (1 / 2 : ℝ)) (hI2.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul]
  rw [hlhs]
  have hH : Integrable (fun z => D.H1 a z + D.H2 a z) D.μP :=
    (D.H1_integrable ha haδ).add (D.H2_integrable ha haδ)
  rw [← integral_add (D.H1_integrable ha haδ) (D.H2_integrable ha haδ)]
  have hH' : Integrable (fun z => D.H1 a z + D.H2 a z)
      ((volume.restrict D.K).prod (volume.restrict (Ioc D.s D.t))) := by
    rw [← μP_eq]; exact hH
  rw [μP_eq, integral_prod _ hH']
  refine setIntegral_congr_fun D.K_measurable fun x hx => ?_
  have hpt := D.pointwise_identity ha haδ hx
  rw [intervalIntegral.integral_of_le D.hst.le] at hpt
  have e1 : (1 / 2 : ℝ) * (D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2) -
        (1 / 2 : ℝ) * (D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2) =
      (1 / 2 : ℝ) * D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2 -
        (1 / 2 : ℝ) * D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2 := by ring
  show _ = ∫ σ in Ioc D.s D.t, (D.H1 a (x, σ) + D.H2 a (x, σ))
  rw [e1, hpt]
  rfl

end Data

end PDE.Parabolic.Energy
