module

public import PDEFoundation.Monotonicity.ACF.Interface
public import PDEFoundation.Analysis.HilbertPolar
public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.Monotonicity.Core.BallDivergencePolar

/-!
# Polar coordinates for integrable integrands, with a.e. slice integrability

For an integrable `g : Vec d → ℝ` (`d ≥ 1`): for a.e. `ρ > 0` the slice over `∂B_ρ` is integrable
(`SphereIntegrable`), the function `ρ ↦ sphereIntegral 0 ρ g` is integrable on `(0, ∞)`, and
`∫ g = ∫_{ρ > 0} sphereIntegral 0 ρ g`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

local notation "𝔼" => HilbertVec d

/-- Fubini part of the polar decomposition on `HilbertVec d`. -/
theorem polar_hilbert_fubini [NeZero d] {G : 𝔼 → ℝ} (hG : Integrable G) :
    (∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
        Integrable (fun ω : Metric.sphere (0 : 𝔼) 1 => G (r • (ω : 𝔼)))
          ((volume : Measure 𝔼).toSphere)) ∧
      IntegrableOn (fun r : ℝ => r ^ (d - 1) *
        ∫ ω : Metric.sphere (0 : 𝔼) 1, G (r • (ω : 𝔼)) ∂((volume : Measure 𝔼).toSphere))
        (Ioi (0 : ℝ)) := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hdim : Module.finrank ℝ 𝔼 = d := by
    calc
      Module.finrank ℝ 𝔼 = Module.finrank ℝ (Fin d → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).finrank_eq
      _ = d := by simp
  have hmp := (volume : Measure 𝔼).measurePreserving_homeomorphUnitSphereProd
  set H : Metric.sphere (0 : 𝔼) 1 × Ioi (0 : ℝ) → ℝ := fun p => G ((p.2 : ℝ) • (p.1 : 𝔼))
    with hH
  have hHcomp : (fun z : ({0}ᶜ : Set 𝔼) => H (homeomorphUnitSphereProd 𝔼 z))
      = fun z : ({0}ᶜ : Set 𝔼) => G (z : 𝔼) := by
    funext z
    simp only [hH]
    have h := (homeomorphUnitSphereProd 𝔼).symm_apply_apply z
    have h2 := congrArg (fun w : ({0}ᶜ : Set 𝔼) => (w : 𝔼)) h
    change ((homeomorphUnitSphereProd 𝔼).symm (homeomorphUnitSphereProd 𝔼 z) : 𝔼) = (z : 𝔼) at h2
    rw [homeomorphUnitSphereProd_symm_apply_coe] at h2
    rw [h2]
  have hHint : Integrable H
      ((volume : Measure 𝔼).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have hcomp : (H ∘ (homeomorphUnitSphereProd 𝔼)) = fun z : ({0}ᶜ : Set 𝔼) => G (z : 𝔼) :=
      hHcomp
    rw [hcomp]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : 𝔼)).compl).mp
      hG.integrableOn
  constructor
  · have h1 := hHint.prod_left_ae
    have h2 : ∀ᵐ y ∂(Measure.comap Subtype.val (volume : Measure ℝ)),
        Integrable (fun x => H (x, y)) ((volume : Measure 𝔼).toSphere) := by
      have h3 : (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1)) =
          (Measure.comap Subtype.val (volume : Measure ℝ)).withDensity
            (fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ 𝔼 - 1))) := rfl
      rw [h3, ae_withDensity_iff (by fun_prop)] at h1
      filter_upwards [h1] with y hy
      exact hy (ENNReal.ofReal_pos.mpr (pow_pos y.2 _)).ne'
    exact (ae_restrict_iff_subtype (μ := (volume : Measure ℝ)) measurableSet_Ioi
      (p := fun r : ℝ => Integrable (fun ω : Metric.sphere (0 : 𝔼) 1 => G (r • (ω : 𝔼)))
        ((volume : Measure 𝔼).toSphere))).mpr h2
  · have h1 := hHint.integral_prod_right
    have h3 : (Measure.volumeIoiPow (Module.finrank ℝ 𝔼 - 1)) =
        (Measure.comap Subtype.val (volume : Measure ℝ)).withDensity
          (fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (Module.finrank ℝ 𝔼 - 1))) := rfl
    rw [h3] at h1
    have h4 := (integrable_withDensity_iff_integrable_smul
      (μ := Measure.comap Subtype.val (volume : Measure ℝ))
      (f := fun r : Ioi (0 : ℝ) => Real.toNNReal ((r : ℝ) ^ (Module.finrank ℝ 𝔼 - 1)))
      (by fun_prop)).mp (by simpa only [ENNReal.ofReal] using h1)
    have h5 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi (μ := (volume : Measure ℝ))
      (f := fun t : ℝ => Real.toNNReal (t ^ (Module.finrank ℝ 𝔼 - 1)) •
        ∫ ω : Metric.sphere (0 : 𝔼) 1, G (t • (ω : 𝔼)) ∂((volume : Measure 𝔼).toSphere))).mpr h4
    refine h5.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt ht) _), smul_eq_mul,
      hdim]

theorem toVec_smul_slice (g : Vec d → ℝ) (ρ : ℝ) (ω : Metric.sphere (0 : 𝔼) 1) :
    (g ∘ (Internal.toHilbert (d := d)).symm) (ρ • (ω : 𝔼)) =
      g ((0 : Vec d) + ρ • (ω : 𝔼).toVec) := by
  have h : (ρ • (ω : 𝔼)).toVec = (0 : Vec d) + ρ • (ω : 𝔼).toVec := by
    ext i; simp [HilbertVec.toVec_apply]
  exact congrArg g h

/-- **Polar coordinates for an integrable integrand.**  For integrable `g` on `Vec d`
(`d ≥ 1`): a.e. slice integrability, integrability of the slice-integral function on `(0,∞)`, and
`∫ g = ∫_{ρ>0} sphereIntegral 0 ρ g`. -/
theorem polar_package [NeZero d] {g : Vec d → ℝ} (hg : Integrable g) :
    (∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))), SphereIntegrable ρ g) ∧
      IntegrableOn (fun ρ => sphereIntegral (0 : Vec d) ρ g) (Ioi (0 : ℝ)) ∧
      ∫ x, g x = ∫ ρ in Ioi (0 : ℝ), sphereIntegral (0 : Vec d) ρ g := by
  set G : 𝔼 → ℝ := g ∘ (Internal.toHilbert (d := d)).symm with hGdef
  have hGint : Integrable G := by
    have := Internal.measurePreserving_toHilbert_symm (d := d)
    exact (this.integrable_comp_emb
      (Internal.toHilbert (d := d)).symm.toHomeomorph.measurableEmbedding).mpr hg
  obtain ⟨h1, h2⟩ := polar_hilbert_fubini hGint
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h1] with ρ hρ
    unfold SphereIntegrable
    refine hρ.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact toVec_smul_slice g ρ ω
  · refine h2.congr_fun (fun ρ _ => ?_) measurableSet_Ioi
    simp only [sphereIntegral]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => toVec_smul_slice g ρ ω)
  · have htr : ∫ x, g x = ∫ z, G z := by
      rw [← Internal.measurePreserving_toHilbert.integral_comp
        (Internal.toHilbert (d := d)).toHomeomorph.measurableEmbedding G]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [G])
    rw [htr, Internal.integral_eq_integral_Ioi_sphere hGint]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
    simp only [sphereIntegral, smul_eq_mul, Internal.sphereMeasure]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => toVec_smul_slice g ρ ω)

end

end PDE
