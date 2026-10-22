module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Probability-kernel convolution in `Lᵖ` -/

@[expose] public section

open scoped ENNReal Pointwise Convolution

namespace PDE

open MeasureTheory

noncomputable section

private theorem isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ}
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ μ)
    (hρOne : ∫ x, ρ x ∂μ = 1) :
    IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρInt
    (ae_of_all _ hρNonneg), hρOne]
  simp

private theorem lintegral_comp_sub_right
    {d : ℕ} (f : Vec d → ℝ≥0∞) (hf : Measurable f)
    (t : Vec d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) =
      ∫⁻ x, f x ∂(volume : Measure (Vec d)) := by
  have heq :
      (fun x => f (x - t)) =
        f ∘ ((· + (-t)) : Vec d → Vec d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap :
      Measure.map (fun x : Vec d => x + (-t))
          (volume : Measure (Vec d)) =
        volume := by
    simpa using
      (map_add_right_eq_self
        (μ := (volume : Measure (Vec d))) (-t))
  rw [hmap]

private theorem fubini_translation_key
    {d : ℕ} (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ)
    (p : ℝ) (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t,
        ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
          ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) *
        (∫⁻ x, (ENNReal.ofReal |g x|) ^ p
          ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · apply Measurable.aemeasurable
      apply Measurable.pow_const
      exact
        ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp
            (hg.comp (measurable_fst.sub measurable_snd)))
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x,
          ρ t * (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume =
        ∫⁻ t, ρ t *
          ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
            ∂volume ∂volume := by
    congr 1
    ext t
    exact
      lintegral_const_mul _ <|
        Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp
              (hg.comp
                (measurable_id.sub measurable_const)))) p
  rw [hfactor]
  have htrans :
      ∀ t,
        ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p
            ∂(volume : Measure (Vec d)) =
          ∫⁻ x, (ENNReal.ofReal |g x|) ^ p
            ∂volume := by
    intro t
    exact
      lintegral_comp_sub_right _
        (Measurable.pow_const
          (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private theorem integral_withDensity_ofReal_eq_integral_mul
    {d : ℕ} {f g : Vec d → ℝ}
    (hfNonneg : ∀ x, 0 ≤ f x)
    (hfMeas : AEMeasurable f volume) :
    ∫ x, g x
        ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq :
      (fun x => ENNReal.ofReal (f x)) =
        fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hfNonneg x),
      Real.toNNReal_of_nonneg (hfNonneg x)]
  rw [heq]
  rw [integral_withDensity_eq_integral_smul₀
    (hfMeas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (hfNonneg x)]

private theorem young_convolution_nonneg_integral_one
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ volume)
    (hρOne : ∫ x, ρ x = 1)
    (hρMeas : Measurable ρ)
    (hgMeas : Measurable g) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume := by
  have hpNeZero : p ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpPos : 0 < p.toReal :=
    ENNReal.toReal_pos hpNeZero hpTop
  have hpOne : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact
      (ENNReal.toReal_le_toReal
        ENNReal.one_ne_top hpTop).mpr hp
  let μ : Measure (Vec d) :=
    volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_withDensity_ofReal
      hρNonneg hρInt hρOne
  have hconvMeas :
      AEStronglyMeasurable
        (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume :=
    (hρMeas.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ)
      hgMeas.aestronglyMeasurable).integral_prod_right'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop hconvMeas]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpNeZero hpTop
    hgMeas.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _
    (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini :=
    fubini_translation_key (d := d)
      (fun t => ENNReal.ofReal (ρ t)) g p.toReal
      hρMeas.ennreal_ofReal hgMeas
  have hρLintegralOne :
      ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρInt
      (ae_of_all _ hρNonneg), hρOne]
    simp
  have hpointwise :
      ∀ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
            p.toReal ≤
          ∫⁻ t,
            ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal
            ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heqIntegral :
        ∫ t, ρ t * g (x - t) =
          ∫ t, g (x - t) ∂μ := by
      symm
      exact
        integral_withDensity_ofReal_eq_integral_mul
          hρNonneg hρMeas.aemeasurable
    rw [heqIntegral]
    by_cases hgInt :
        Integrable (fun t => g (x - t)) μ
    · by_cases hgPowInt :
          Integrable
            (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen :=
          abs_integral_rpow_le_integral_abs_rpow
            (μ := μ) hpOne hgInt hgPowInt
        have heqPow :
            ∫ t, |g (x - t)| ^ p.toReal ∂μ =
              (∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal
                  ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul
            hρNonneg hρMeas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρNonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          · exact
              ae_of_all _ fun t =>
                mul_nonneg (hρNonneg t)
                  (Real.rpow_nonneg (abs_nonneg _) _)
          · have hAbsPowMeas :
                Measurable
                  (fun t =>
                    |g (x - t)| ^ p.toReal) := by
              have hcont :
                  Continuous
                    (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const
                  (fun _ => Or.inr hpPos.le)
              exact
                hcont.measurable.comp
                  (hgMeas.comp
                    (measurable_const.sub measurable_id))
            exact
              (hρMeas.mul hAbsPowMeas).aestronglyMeasurable
        calc
          ENNReal.ofReal
                |∫ t, g (x - t) ∂μ| ^ p.toReal =
              ENNReal.ofReal
                (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          _ ≤
              ENNReal.ofReal
                (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ =
              ENNReal.ofReal
                ((∫⁻ t,
                    ENNReal.ofReal (ρ t) *
                      (ENNReal.ofReal |g (x - t)|) ^
                        p.toReal
                    ∂volume).toReal) := by
            rw [heqPow]
          _ ≤
              ∫⁻ t,
                ENNReal.ofReal (ρ t) *
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnotFinite :
            ∫⁻ t,
                ENNReal.ofReal (ρ t) *
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                ∂volume =
              ⊤ := by
          have heq :
              ∫⁻ t,
                  ENNReal.ofReal (ρ t) *
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal
                  ∂volume =
                ∫⁻ t,
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂μ := by
            have hsub :
                Measurable (fun t : Vec d => x - t) :=
              measurable_const.sub measurable_id
            have hAbsMeas :
                Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp
                (hgMeas.comp hsub)
            have hMeasPow :
                Measurable
                  (fun t =>
                    (ENNReal.ofReal |g (x - t)|) ^
                      p.toReal) :=
              Measurable.pow_const
                hAbsMeas.ennreal_ofReal p.toReal
            symm
            convert
              lintegral_withDensity_eq_lintegral_mul
                volume hρMeas.ennreal_ofReal hMeasPow
              using 2
          rw [heq]
          have hAbsPowNonneg :
              ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t =>
              Real.rpow_nonneg (abs_nonneg _) _
          have hAbsPowMeas :
              Measurable
                (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont :
                Continuous
                  (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const
                (fun _ => Or.inr hpPos.le)
            have hsub :
                Measurable (fun t : Vec d => x - t) :=
              measurable_const.sub measurable_id
            exact
              hcont.measurable.comp (hgMeas.comp hsub)
          have htop :
              ∫⁻ t,
                  (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂μ =
                ⊤ := by
            rw [←
              lintegral_ofReal_ne_top_iff_integrable
                hAbsPowMeas.aestronglyMeasurable
                (ae_of_all _ hAbsPowNonneg)] at hgPowInt
            push Not at hgPowInt
            convert hgPowInt using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg
              (abs_nonneg _) hpPos.le]
          rw [htop]
        simp [hnotFinite]
    · rw [integral_undef hgInt]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hpPos]
      exact zero_le
  calc
    ∫⁻ x,
        ‖convolution ρ g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^
          p.toReal
        ∂volume ≤
      ∫⁻ x, ∫⁻ t,
          ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal
          ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ =
        (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal
            ∂volume) :=
      hfubini
    _ =
        1 *
          (∫⁻ x,
            (ENNReal.ofReal |g x|) ^ p.toReal
            ∂volume) := by
      rw [hρLintegralOne]
    _ =
        ∫⁻ x,
          (ENNReal.ofReal |g x|) ^ p.toReal
          ∂volume := one_mul _
    _ =
        ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

private theorem young_convolution_nonneg_integral_one_of_aemeasurable
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ volume)
    (hρOne : ∫ x, ρ x = 1)
    (hρMeas : Measurable ρ)
    (hgMeas : AEMeasurable g volume) :
    eLpNorm
        (convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        p volume ≤
      eLpNorm g p volume := by
  let g' : Vec d → ℝ :=
    hgMeas.mk g
  have hconv :
      convolution ρ g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution ρ g'
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    simpa [g'] using
      (convolution_congr
        (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure (Vec d)))
        (h1 := Filter.EventuallyEq.rfl)
        (h2 := hgMeas.ae_eq_mk))
  rw [hconv]
  calc
    eLpNorm
          (convolution ρ g'
            (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          p volume ≤
        eLpNorm g' p volume :=
      young_convolution_nonneg_integral_one
        hp hpTop hρNonneg hρInt hρOne hρMeas
        hgMeas.measurable_mk
    _ = eLpNorm g p volume :=
      eLpNorm_congr_ae hgMeas.ae_eq_mk.symm

/-- Convolution by a scaled convex approximation kernel is globally smooth and
is a contraction on every finite `Lᵖ` with `p ≥ 1`. -/
theorem contDiff_memLp_convolution_scaledConvexApproxKernel
    {d : ℕ} {ρ f : Vec d → ℝ} {a : ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (ha : 0 < a)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hf : MemLp f p volume) :
    ContDiff ℝ (⊤ : ℕ∞)
        (scaledConvexApproxKernel ρ a ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ∧
      MemLp
        (scaledConvexApproxKernel ρ a ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] f) p volume ∧
      eLpNorm
          (scaledConvexApproxKernel ρ a ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] f) p volume ≤
        eLpNorm f p volume := by
  let K := scaledConvexApproxKernel ρ a
  let g := convolution K f (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    apply HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    · exact hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
    · exact contDiff_scaledConvexApproxKernel hρ a
    · exact hf.locallyIntegrable hp
  have hnorm : eLpNorm g p volume ≤ eLpNorm f p volume := by
    apply young_convolution_nonneg_integral_one_of_aemeasurable hp hpTop
    · exact scaledConvexApproxKernel_nonneg hρ ha
    · exact integrable_scaledConvexApproxKernel hρ ha
    · exact integral_scaledConvexApproxKernel hρ ha
    · exact measurable_scaledConvexApproxKernel hρ.smooth.continuous a
    · exact hf.aestronglyMeasurable.aemeasurable
  have hg : MemLp g p volume := by
    exact lt_of_le_of_lt hnorm hf.eLpNorm_lt_top
  exact ⟨hsmooth, hg, hnorm⟩

end

end PDE
