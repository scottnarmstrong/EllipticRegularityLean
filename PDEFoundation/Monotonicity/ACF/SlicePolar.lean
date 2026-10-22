module

public import PDEFoundation.Monotonicity.ACF.SliceRayleigh
public import PDEFoundation.Monotonicity.Core.BallDivergencePolar

/-!
# ACF-S2: polar slicing of integrable functions

For `G` integrable on `Vec d` the radial slice integrals
`r ↦ sphereIntegral 0 1 (fun y => G (r • y))` are defined (the slice is integrable) for almost
every `r > 0`, and `∫ G = ∫_{r > 0} r^(d-1) · slice G r`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The slice integral of `G` at radius `r`: `∫_{S^{d-1}} G (r ω) dσ`. -/
def sliceIntegral (G : Vec d → ℝ) (r : ℝ) : ℝ :=
  sphereIntegral (0 : Vec d) 1 (fun y => G (r • y))

theorem sliceIntegral_eq (G : Vec d → ℝ) (r : ℝ) :
    sliceIntegral G r =
      ∫ ω : Metric.sphere (0 : HilbertVec d) 1, G (r • (ω : HilbertVec d).toVec)
        ∂((volume : Measure (HilbertVec d)).toSphere) := by
  simp [sliceIntegral, sphereIntegral]

/-- Slice integrability of `G` at radius `r`. -/
def SliceIntegrable (G : Vec d → ℝ) (r : ℝ) : Prop :=
  Integrable (fun ω : Metric.sphere (0 : HilbertVec d) 1 => G (r • (ω : HilbertVec d).toVec))
    ((volume : Measure (HilbertVec d)).toSphere)

theorem smul_homeomorphUnitSphereProd_eq' (z : ({0}ᶜ : Set (HilbertVec d))) :
    ((homeomorphUnitSphereProd (HilbertVec d) z).2 : ℝ) •
      ((homeomorphUnitSphereProd (HilbertVec d) z).1 : HilbertVec d) = (z : HilbertVec d) := by
  have h := (homeomorphUnitSphereProd (HilbertVec d)).symm_apply_apply z
  have h2 := congrArg (fun w : ({0}ᶜ : Set (HilbertVec d)) => (w : HilbertVec d)) h
  change ((homeomorphUnitSphereProd (HilbertVec d)).symm
    (homeomorphUnitSphereProd (HilbertVec d) z) : HilbertVec d) = (z : HilbertVec d) at h2
  rw [homeomorphUnitSphereProd_symm_apply_coe] at h2
  exact h2

theorem polar_slices [NeZero d] {G : Vec d → ℝ} (hG : Integrable G) :
    (∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), SliceIntegrable G r) ∧
    IntegrableOn (fun r => r ^ (d - 1) * sliceIntegral G r) (Ioi (0 : ℝ)) ∧
    ∫ x, G x = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * sliceIntegral G r := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hdim : Module.finrank ℝ (HilbertVec d) = d := by
    calc
      Module.finrank ℝ (HilbertVec d) = Module.finrank ℝ (Fin d → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
      _ = d := by simp
  set G' : HilbertVec d → ℝ := fun z => G z.toVec with hG'def
  have hG' : Integrable G' := by
    have := (Internal.measurePreserving_toHilbert_symm (d := d)).integrable_comp_emb
      (Internal.toHilbert (d := d)).symm.toHomeomorph.measurableEmbedding (g := G)
    exact this.2 hG
  have hmp := (volume : Measure (HilbertVec d)).measurePreserving_homeomorphUnitSphereProd
  set H : Metric.sphere (0 : HilbertVec d) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => G' ((p.2 : ℝ) • (p.1 : HilbertVec d)) with hH
  have hHcomp : (fun z : ({0}ᶜ : Set (HilbertVec d)) => H (homeomorphUnitSphereProd (HilbertVec d) z))
      = fun z : ({0}ᶜ : Set (HilbertVec d)) => G' (z : HilbertVec d) := by
    funext z
    simp only [hH]
    rw [smul_homeomorphUnitSphereProd_eq' z]
  have hHint : Integrable H
      ((volume : Measure (HilbertVec d)).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (HilbertVec d) - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have hcomp : (H ∘ (homeomorphUnitSphereProd (HilbertVec d))) =
        fun z : ({0}ᶜ : Set (HilbertVec d)) => G' (z : HilbertVec d) := hHcomp
    rw [hcomp]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : HilbertVec d)).compl).mp
      hG'.integrableOn
  have step1 : (∫ z, G' z)
      = ∫ z : ({0}ᶜ : Set (HilbertVec d)), G' (z : HilbertVec d)
          ∂(Measure.comap Subtype.val volume) := by
    rw [integral_subtype_comap (measurableSet_singleton (0 : HilbertVec d)).compl (fun z => G' z),
      restrict_compl_singleton]
  have step2 : (∫ z : ({0}ᶜ : Set (HilbertVec d)), G' (z : HilbertVec d)
        ∂(Measure.comap Subtype.val volume))
      = ∫ p, H p ∂((volume : Measure (HilbertVec d)).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (HilbertVec d) - 1))) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) H, hHcomp]
  have step3 := integral_prod_symm H hHint
  have hsl := hHint.prod_left_ae
  have hint2 := hHint.integral_prod_right
  have hHr : ∀ (r : Ioi (0 : ℝ)) (ω : Metric.sphere (0 : HilbertVec d) 1),
      H (ω, r) = G ((r : ℝ) • (ω : HilbertVec d).toVec) := fun r ω => rfl
  have hn : Module.finrank ℝ (HilbertVec d) - 1 = d - 1 := by rw [hdim]
  have hmeas : Measurable fun r : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ (HilbertVec d) - 1)) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  refine ⟨?_, ?_, ?_⟩
  · rw [ae_restrict_iff_subtype measurableSet_Ioi]
    have h1 : ∀ᵐ r : Ioi (0 : ℝ) ∂(Measure.volumeIoiPow (Module.finrank ℝ (HilbertVec d) - 1)),
        SliceIntegrable G r := hsl.mono fun r hr => by simpa only [SliceIntegrable, hHr] using hr
    rw [Measure.volumeIoiPow, ae_withDensity_iff hmeas] at h1
    exact h1.mono fun r hr => hr (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos r.2 _)
  · have h2 : Integrable (fun r : Ioi (0 : ℝ) => ∫ ω, H (ω, r)
        ∂((volume : Measure (HilbertVec d)).toSphere))
        (Measure.volumeIoiPow (Module.finrank ℝ (HilbertVec d) - 1)) := hint2
    rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h2
    refine (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).2 (h2.congr
      (Filter.Eventually.of_forall fun r => ?_))
    simp only [Function.comp_apply, smul_eq_mul, hn]
    rw [ENNReal.toReal_ofReal (pow_nonneg r.2.le _), sliceIntegral_eq]
    simp only [hHr]
  · have hGG : ∫ x, G x = ∫ z, G' z :=
      (Internal.measurePreserving_toHilbert_symm (d := d)).integral_comp
        (Internal.toHilbert (d := d)).symm.toHomeomorph.measurableEmbedding G |>.symm
    rw [hGG, step1, step2, step3]
    simp only [Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul
      (show Measurable fun r : Ioi (0 : ℝ) =>
          Real.toNNReal ((r : ℝ) ^ (Module.finrank ℝ (HilbertVec d) - 1)) from
        (measurable_subtype_coe.pow_const _).real_toNNReal)]
    simp only [hHr]
    rw [integral_subtype_comap measurableSet_Ioi
      (fun t : ℝ => Real.toNNReal (t ^ (Module.finrank ℝ (HilbertVec d) - 1)) •
        ∫ ω, G (t • (ω : HilbertVec d).toVec) ∂((volume : Measure (HilbertVec d)).toSphere))]
    rw [hn]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt ht) _), smul_eq_mul,
      sliceIntegral_eq]

theorem sliceIntegral_nonneg {G : Vec d → ℝ} (hG : ∀ x, 0 ≤ G x) (r : ℝ) :
    0 ≤ sliceIntegral G r := by
  rw [sliceIntegral_eq]
  exact integral_nonneg fun _ => hG _

theorem SliceIntegrable.sliceIntegral_sub {G H : Vec d → ℝ} {r : ℝ} (hG : SliceIntegrable G r)
    (hH : SliceIntegrable H r) :
    sliceIntegral (fun x => G x - H x) r = sliceIntegral G r - sliceIntegral H r := by
  simp only [sliceIntegral_eq]
  exact integral_sub hG hH

theorem abs_sliceIntegral_le (G : Vec d → ℝ) (r : ℝ) :
    |sliceIntegral G r| ≤ sliceIntegral (fun x => |G x|) r := by
  simp only [sliceIntegral_eq]
  exact abs_integral_le_integral_abs

theorem integrableOn_mul_abs_sliceIntegral [NeZero d] {G : Vec d → ℝ} (hG : Integrable G) :
    IntegrableOn (fun r => r ^ (d - 1) * |sliceIntegral G r|) (Ioi (0 : ℝ)) := by
  obtain ⟨-, hint, -⟩ := polar_slices hG
  refine IntegrableOn.congr_fun (Integrable.norm hint) (fun r hr => ?_) measurableSet_Ioi
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt (mem_Ioi.1 hr)) _)]

/-- `L¹(r^(d-1) dr)` bound for the slice integrals. -/
theorem integral_abs_sliceIntegral_le [NeZero d] {G : Vec d → ℝ} (hG : Integrable G) :
    ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * |sliceIntegral G r| ≤ ∫ x, |G x| := by
  obtain ⟨-, hint2, heq⟩ := polar_slices hG.abs
  rw [heq]
  refine setIntegral_mono_on (integrableOn_mul_abs_sliceIntegral hG) hint2 measurableSet_Ioi
    fun r hr => ?_
  exact mul_le_mul_of_nonneg_left (abs_sliceIntegral_le G r) (pow_nonneg (le_of_lt hr) _)

/-- If `Gn → G` in `L¹(Vec d)`, then along a subsequence the slice integrals converge for almost
every radius. -/
theorem exists_subseq_sliceIntegral_tendsto [NeZero d] {Gn : ℕ → Vec d → ℝ} {G : Vec d → ℝ}
    (hGn : ∀ n, Integrable (Gn n)) (hG : Integrable G)
    (h : Filter.Tendsto (fun n => ∫ x, |Gn n x - G x|) Filter.atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      SliceIntegrable G r ∧ (∀ k, SliceIntegrable (Gn (φ k)) r) ∧
      Filter.Tendsto (fun k => sliceIntegral (Gn (φ k)) r) Filter.atTop
        (nhds (sliceIntegral G r)) := by
  set D : ℕ → Vec d → ℝ := fun n x => Gn n x - G x with hD
  have hDint : ∀ n, Integrable (D n) := fun n => (hGn n).sub hG
  set F : ℕ → ℝ → ℝ := fun n r => r ^ (d - 1) * |sliceIntegral (D n) r| with hF
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) :=
    fun n => (integrableOn_mul_abs_sliceIntegral (hDint n))
  have hFnonneg : ∀ n, ∀ r ∈ Ioi (0 : ℝ), 0 ≤ F n r := fun n r hr =>
    mul_nonneg (pow_nonneg (le_of_lt hr) _) (abs_nonneg _)
  have hF1 : Filter.Tendsto (fun n => ∫ r in Ioi (0 : ℝ), F n r) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => setIntegral_nonneg measurableSet_Ioi (hFnonneg n)) (fun n => ?_) h
    exact integral_abs_sliceIntegral_le (hDint n)
  have hE : Filter.Tendsto (fun n => eLpNorm (F n - 0) 1 (volume.restrict (Ioi (0 : ℝ))))
      Filter.atTop (nhds 0) := by
    have hnn : ∀ n, 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] F n :=
      fun n => (ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall (hFnonneg n))
    have : ∀ n, eLpNorm (F n - 0) 1 (volume.restrict (Ioi (0 : ℝ))) =
        ENNReal.ofReal (∫ r in Ioi (0 : ℝ), F n r) := fun n => by
      have _hm : AEStronglyMeasurable (F n) (volume.restrict (Ioi (0 : ℝ))) :=
        (hFint n).aestronglyMeasurable
      rw [sub_zero, eLpNorm_one_eq_lintegral_enorm,
        ofReal_integral_eq_lintegral_ofReal (hFint n) (hnn n)]
      exact (lintegral_congr_ae ((hnn n).mono fun r hr => by
        simp [Real.enorm_eq_ofReal hr]))
      exact _hm
    simp only [this]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal hF1
  have hM : TendstoInMeasure (volume.restrict (Ioi (0 : ℝ))) F Filter.atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hE
  obtain ⟨φ, hφ, hae⟩ := hM.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hs1 := (polar_slices hG).1
  have hs2 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n, SliceIntegrable (Gn n) r :=
    ae_all_iff.2 fun n => (polar_slices (hGn n)).1
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) := ae_restrict_mem measurableSet_Ioi
  filter_upwards [hs1, hs2, hae, hmem] with r h1 h2 h3 h4
  refine ⟨h1, fun k => h2 _, ?_⟩
  have hpos : 0 < r ^ (d - 1) := pow_pos h4 _
  have h5 : Filter.Tendsto (fun k => |sliceIntegral (D (φ k)) r|) Filter.atTop (nhds 0) := by
    have := h3.const_mul (r ^ (d - 1))⁻¹
    simp only [hF, mul_zero] at this
    refine this.congr fun k => ?_
    field_simp
  have h6 : ∀ k, sliceIntegral (D (φ k)) r = sliceIntegral (Gn (φ k)) r - sliceIntegral G r :=
    fun k => (h2 _).sliceIntegral_sub h1
  simp only [h6] at h5
  have := (tendsto_zero_iff_abs_tendsto_zero _).2 h5
  simpa using this.add_const (sliceIntegral G r)

end

end PDE
