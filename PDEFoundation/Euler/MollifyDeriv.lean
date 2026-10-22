module

public import PDEFoundation.Euler.MollifySpaceTime
public import PDEFoundation.Euler.MollifySymm
public import PDEFoundation.Euler.GradLimitBasic

/-!
# Derivatives of the mollification: kernel formula, bound, measurability

`∂ⱼ (molK a ⋆ f) = (∂ⱼ molK a) ⋆ f`, so `|∂ⱼ (molK a ⋆ f)| ≤ ‖∂ⱼ molK a‖₁ ‖f‖_∞`, and the space-time
convolution with any continuous kernel is a.e. strongly measurable for `eulerMeasureExt`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace PDE

theorem pd_mollify_apply {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume)
    (j : Fin 2) (x : Vec 2) :
    pd j (mollify a f) x = ∫ t, pd j (molK a) t * f (x - t) := by
  have h := (molK_hasCompactSupport ha).hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (molK_contDiff a |>.of_le (by simp)) hf x
  have hex : ConvolutionExistsAt (fderiv ℝ (molK a)) f x
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 2)) volume := by
    refine ((molK_hasCompactSupport ha).fderiv ℝ).convolutionExists_left _
      ((molK_contDiff a).continuous_fderiv (by simp)) hf x
  rw [pd_def]
  have h2 : fderiv ℝ (mollify a f) x = _ := h.fderiv
  rw [h2]
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hex]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [pd_def]

theorem continuous_pd_molK (a : ℝ) (j : Fin 2) : Continuous (pd j (molK a)) :=
  continuous_pd_of_contDiff (molK_contDiff a) j

theorem hasCompactSupport_pd_molK {a : ℝ} (ha : 0 < a) (j : Fin 2) : HasCompactSupport (pd j (molK a)) := by
  have h := ((molK_hasCompactSupport ha).fderiv ℝ).comp_left
    (g := fun A : Vec 2 →L[ℝ] ℝ => A (basisVec j)) (by simp)
  exact h

theorem integrable_pd_molK {a : ℝ} (ha : 0 < a) (j : Fin 2) : Integrable (pd j (molK a)) :=
  (continuous_pd_molK a j).integrable_of_hasCompactSupport (hasCompactSupport_pd_molK ha j)

theorem integrable_pd_molK_mul {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume)
    (j : Fin 2) (x : Vec 2) : Integrable (fun t => pd j (molK a) t * f (x - t)) := by
  have := (hasCompactSupport_pd_molK ha j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (continuous_pd_molK a j) hf x
  simpa [ConvolutionExistsAt] using this

/-- `L¹` norm of `∂ⱼ molK a`. -/
noncomputable def pdMolKNorm (a : ℝ) (j : Fin 2) : ℝ := ∫ t, |pd j (molK a) t|

theorem abs_pd_mollify_le {a : ℝ} (ha : 0 < a) {f : Vec 2 → ℝ} (hf : LocallyIntegrable f volume) {B : ℝ}
    (hB : ∀ᵐ y, |f y| ≤ B) (j : Fin 2) (x : Vec 2) :
    |pd j (mollify a f) x| ≤ pdMolKNorm a j * B := by
  rw [pd_mollify_apply ha hf j x]
  have hex := integrable_pd_molK_mul ha hf j x
  have hK := integrable_pd_molK ha j
  calc |∫ t, pd j (molK a) t * f (x - t)| ≤ ∫ t, |pd j (molK a) t * f (x - t)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t => pd j (molK a) t * f (x - t))
    _ ≤ ∫ t, |pd j (molK a) t| * B := by
        refine integral_mono_ae hex.abs (hK.abs.mul_const B) ?_
        have hB' : ∀ᵐ t ∂(volume : Measure (Vec 2)), |f (x - t)| ≤ B :=
          ((volume : Measure (Vec 2)).measurePreserving_sub_left x).quasiMeasurePreserving.ae hB
        filter_upwards [hB'] with t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ = pdMolKNorm a j * B := by rw [integral_mul_const]; rfl

theorem aestronglyMeasurable_convST {T : ℝ} (k : Vec 2 → ℝ) (hk : Continuous k) {u : Vec 2 × ℝ → ℝ}
    (hu : AEStronglyMeasurable u (eulerMeasureExt T)) :
    AEStronglyMeasurable (fun z : Vec 2 × ℝ => ∫ t, k t * u (z.1 - t, z.2)) (eulerMeasureExt T) := by
  set μ := eulerMeasureExt T with hμ
  have hshear : ∀ s : Vec 2, MeasurePreserving (fun p : Vec 2 × ℝ => (p.1 - s, p.2)) μ μ := fun s =>
    (measurePreserving_sub_right (volume : Measure (Vec 2)) s).prod
      (MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) T)))
  have hskew : MeasurePreserving (fun q : Vec 2 × (Vec 2 × ℝ) => (q.1, (q.2.1 - q.1, q.2.2)))
      ((volume : Measure (Vec 2)).prod μ) ((volume : Measure (Vec 2)).prod μ) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure (Vec 2)))
      (g := fun (s : Vec 2) (p : Vec 2 × ℝ) => (p.1 - s, p.2)) ?_ ?_
    · exact (measurable_snd.fst.sub measurable_fst).prodMk measurable_snd.snd
    · exact Filter.Eventually.of_forall fun s => (hshear s).map_eq
  have hΨ : MeasurePreserving (fun q : (Vec 2 × ℝ) × Vec 2 => (q.2, (q.1.1 - q.2, q.1.2)))
      (μ.prod (volume : Measure (Vec 2))) ((volume : Measure (Vec 2)).prod μ) :=
    hskew.comp (Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure (Vec 2))))
  have hu2 : AEStronglyMeasurable (fun q : Vec 2 × (Vec 2 × ℝ) => u q.2)
      ((volume : Measure (Vec 2)).prod μ) := hu.comp_snd
  have hΘ : AEStronglyMeasurable (fun q : (Vec 2 × ℝ) × Vec 2 => k q.2 * u (q.1.1 - q.2, q.1.2))
      (μ.prod (volume : Measure (Vec 2))) := by
    have h1 := hu2.comp_measurePreserving hΨ
    have h2 : AEStronglyMeasurable (fun q : (Vec 2 × ℝ) × Vec 2 => k q.2)
        (μ.prod (volume : Measure (Vec 2))) :=
      (Continuous.aestronglyMeasurable hk).comp_snd
    exact h2.mul h1
  exact hΘ.integral_prod_right'

/-- Measurability of `(x,t) ↦ ∂ⱼ (molK a ⋆ u(·,t))(x)`. -/
theorem aestronglyMeasurable_pd_mollifyST {T a : ℝ} (ha : 0 < a) {u : Vec 2 × ℝ → ℝ}
    (hu : AEStronglyMeasurable u (eulerMeasureExt T))
    (hloc : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), LocallyIntegrable (fun x => u (x, t)) volume)
    (j : Fin 2) :
    AEStronglyMeasurable (fun z : Vec 2 × ℝ => pd j (fun x => mollifyST a u (x, z.2)) z.1)
      (eulerMeasureExt T) := by
  refine (aestronglyMeasurable_convST (pd j (molK a)) (continuous_pd_molK a j) hu).congr ?_
  have h1 : ∀ᵐ z ∂(eulerMeasureExt T), LocallyIntegrable (fun x => u (x, z.2)) volume :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Vec 2)))
      (ν := volume.restrict (Icc (0 : ℝ) T))).ae hloc
  filter_upwards [h1] with z hz
  have := pd_mollify_apply ha hz j z.1
  simpa [mollifyST] using this.symm

end PDE
