module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# The affine blow-up map `y ↦ r • y + x₀`

Change-of-variables facts for the map `T y = r • y + x₀` (`r > 0`), which
carries `euclideanBall 0 ρ` onto `euclideanBall x₀ (r * ρ)`:

* `map (T) (volumeOn V) = ofReal ((r ^ d)⁻¹) • volumeOn (translateSet x₀ (r • V))`;
* `∫ y in V, g (T y) = (r ^ d)⁻¹ * ∫ x in translateSet x₀ (r • V), g x`;
* integrability, a.e.-measurability and a.e. statements transfer along `T`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

namespace DGNM

open MeasureTheory

variable {d : ℕ}

/-- The affine map `y ↦ r • y + x₀` as a homeomorphism. -/
noncomputable def affineScale (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addRight x₀)

@[simp]
theorem affineScale_apply (x₀ : Vec d) {r : ℝ} (hr : r ≠ 0) (y : Vec d) :
    affineScale x₀ hr y = r • y + x₀ :=
  rfl

theorem map_affineScale_volumeOn (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (V : Set (Vec d)) :
    Measure.map (fun y => r • y + x₀) (volumeOn V) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volumeOn (translateSet x₀ (r • V)) := by
  have h1 : (fun y : Vec d => r • y + x₀) = (fun z => z + x₀) ∘ (fun y => r • y) :=
    rfl
  rw [h1, ← Measure.map_map (measurable_add_const x₀)
      (show Measurable (fun y : Vec d => r • y) from measurable_id.const_smul r),
    map_smul_volumeOn_of_pos hr V,
    Measure.map_smul,
    (measurePreserving_addRight_restrict_translateSet x₀ (r • V)).map_eq]
  exact (measurable_add_const x₀).aemeasurable

/-- Change of variables along `y ↦ r • y + x₀`. -/
theorem setIntegral_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (V : Set (Vec d)) (g : Vec d → ℝ) :
    ∫ y in V, g (r • y + x₀) =
      (r ^ d)⁻¹ * ∫ x in translateSet x₀ (r • V), g x := by
  calc ∫ y in V, g (r • y + x₀) = (r ^ d)⁻¹ • ∫ z in r • V, g (z + x₀) :=
        setIntegral_comp_smul_of_pos hr V (fun z => g (z + x₀))
    _ = (r ^ d)⁻¹ * ∫ x in translateSet x₀ (r • V), g x := by
        rw [setIntegral_comp_addRight_translateSet, smul_eq_mul]

theorem integrableOn_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {V : Set (Vec d)} {g : Vec d → ℝ}
    (hg : IntegrableOn g (translateSet x₀ (r • V))) :
    IntegrableOn (fun y => g (r • y + x₀)) V := by
  have hmap : Integrable g (Measure.map (fun y => r • y + x₀) (volumeOn V)) := by
    rw [map_affineScale_volumeOn x₀ hr V]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (affineScale x₀ hr.ne').measurableEmbedding.integrable_map_iff.mp hmap

theorem aemeasurable_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {V : Set (Vec d)} {g : Vec d → ℝ}
    (hg : AEMeasurable g (volumeOn (translateSet x₀ (r • V)))) :
    AEMeasurable (fun y => g (r • y + x₀)) (volumeOn V) := by
  have hmap : AEMeasurable g (Measure.map (fun y => r • y + x₀) (volumeOn V)) := by
    rw [map_affineScale_volumeOn x₀ hr V]
    exact hg.smul_measure _
  exact hmap.comp_measurable (affineScale x₀ hr.ne').measurable

/-- A.e. statements transfer along the blow-up map. -/
theorem ae_comp_affineScale_iff (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {V : Set (Vec d)} {P : Vec d → Prop} :
    (∀ᵐ y ∂volumeOn V, P (r • y + x₀)) ↔
      ∀ᵐ x ∂volumeOn (translateSet x₀ (r • V)), P x := by
  have hc : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr d))).ne'
  rw [← Measure.ae_ennreal_smul_measure_iff hc
    (μ := volumeOn (translateSet x₀ (r • V))), ← map_affineScale_volumeOn x₀ hr V]
  exact (affineScale x₀ hr.ne').measurableEmbedding.ae_map_iff.symm

/-- `L^p` seminorms transfer along the blow-up map. -/
theorem eLpNorm_comp_affineScale {E : Type*} [NormedAddCommGroup E] (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (V : Set (Vec d)) (g : Vec d → E) (p : ENNReal) :
    eLpNorm (fun y => g (r • y + x₀)) p (volumeOn V) =
      ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / p).toReal *
        eLpNorm g p (volumeOn (translateSet x₀ (r • V))) := by
  have hc : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr d))).ne'
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero hc, ← map_affineScale_volumeOn x₀ hr V]
  exact ((affineScale x₀ hr.ne').measurableEmbedding.eLpNorm_map_measure).symm

/-- Lower integrals transfer along the blow-up map. -/
theorem setLIntegral_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (V : Set (Vec d)) (g : Vec d → ENNReal) :
    ∫⁻ y in V, g (r • y + x₀) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ x in translateSet x₀ (r • V), g x := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_affineScale_volumeOn x₀ hr V]
  exact ((affineScale x₀ hr.ne').measurableEmbedding.lintegral_map g).symm

/-- Essential suprema transfer along the blow-up map. -/
theorem essSup_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (V : Set (Vec d)) (g : Vec d → ENNReal) :
    essSup (fun y => g (r • y + x₀)) (volumeOn V) =
      essSup g (volumeOn (translateSet x₀ (r • V))) := by
  apply le_antisymm
  · refine essSup_le_of_ae_le _ ?_
    exact (ae_comp_affineScale_iff x₀ hr (P := fun x =>
      g x ≤ essSup g (volumeOn (translateSet x₀ (r • V))))).mpr
        (ENNReal.ae_le_essSup g)
  · refine essSup_le_of_ae_le _ ?_
    exact (ae_comp_affineScale_iff x₀ hr (P := fun x =>
      g x ≤ essSup (fun y => g (r • y + x₀)) (volumeOn V))).mp
        (ENNReal.ae_le_essSup (fun y => g (r • y + x₀)))

/-- Essential infima transfer along the blow-up map. -/
theorem essInf_comp_affineScale (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (V : Set (Vec d)) (g : Vec d → ENNReal) :
    essInf (fun y => g (r • y + x₀)) (volumeOn V) =
      essInf g (volumeOn (translateSet x₀ (r • V))) := by
  apply le_antisymm
  · refine le_essInf_of_ae_le _ ?_
    exact (ae_comp_affineScale_iff x₀ hr (P := fun x =>
      essInf (fun y => g (r • y + x₀)) (volumeOn V) ≤ g x)).mp ae_essInf_le
  · refine le_essInf_of_ae_le _ ?_
    exact (ae_comp_affineScale_iff x₀ hr (P := fun x =>
      essInf g (volumeOn (translateSet x₀ (r • V))) ≤ g x)).mpr ae_essInf_le

/-- The blow-up of a centered ball is the translated scaled ball. -/
theorem translateSet_smul_euclideanBall (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) :
    translateSet x₀ (r • euclideanBall (0 : Vec d) ρ) = euclideanBall x₀ (r * ρ) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  change euclideanSqDist (r⁻¹ • (x - x₀)) 0 < ρ ^ 2 ↔
    euclideanSqDist x x₀ < (r * ρ) ^ 2
  have h : euclideanSqDist (r⁻¹ • (x - x₀)) 0 = (r⁻¹) ^ 2 * euclideanSqDist x x₀ := by
    have := euclideanSqDist_smul_smul r⁻¹ (x - x₀) 0
    rw [smul_zero] at this
    rw [this]
    congr 1
    unfold euclideanSqDist
    congr 1
    ext i
    simp
  rw [h]
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  rw [inv_pow, mul_pow, inv_mul_lt_iff₀ hr2]

/-- Membership in the blown-up ball. -/
theorem affineScale_mem_euclideanBall_iff (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) (y : Vec d) :
    r • y + x₀ ∈ euclideanBall x₀ (r * ρ) ↔ y ∈ euclideanBall (0 : Vec d) ρ := by
  rw [← translateSet_smul_euclideanBall x₀ hr ρ, mem_translateSet_iff_sub_mem,
    add_sub_cancel_right, Set.smul_mem_smul_set_iff₀ hr.ne']

/-! ### Ball forms -/

theorem setIntegral_comp_affineScale_ball (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    (g : Vec d → ℝ) :
    ∫ y in euclideanBall (0 : Vec d) ρ, g (r • y + x₀) =
      (r ^ d)⁻¹ * ∫ x in euclideanBall x₀ (r * ρ), g x := by
  rw [setIntegral_comp_affineScale x₀ hr, translateSet_smul_euclideanBall x₀ hr]

theorem eLpNorm_comp_affineScale_ball {E : Type*} [NormedAddCommGroup E] (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (ρ : ℝ) (g : Vec d → E) (p : ENNReal) :
    eLpNorm (fun y => g (r • y + x₀)) p (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / p).toReal *
        eLpNorm g p (volumeOn (euclideanBall x₀ (r * ρ))) := by
  rw [eLpNorm_comp_affineScale x₀ hr, translateSet_smul_euclideanBall x₀ hr]

theorem essSup_comp_affineScale_ball (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    (g : Vec d → ENNReal) :
    essSup (fun y => g (r • y + x₀)) (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      essSup g (volumeOn (euclideanBall x₀ (r * ρ))) := by
  rw [essSup_comp_affineScale x₀ hr, translateSet_smul_euclideanBall x₀ hr]

theorem essInf_comp_affineScale_ball (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    (g : Vec d → ENNReal) :
    essInf (fun y => g (r • y + x₀)) (volumeOn (euclideanBall (0 : Vec d) ρ)) =
      essInf g (volumeOn (euclideanBall x₀ (r * ρ))) := by
  rw [essInf_comp_affineScale x₀ hr, translateSet_smul_euclideanBall x₀ hr]

theorem ae_comp_affineScale_ball_iff (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    {P : Vec d → Prop} :
    (∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) ρ), P (r • y + x₀)) ↔
      ∀ᵐ x ∂volumeOn (euclideanBall x₀ (r * ρ)), P x := by
  rw [ae_comp_affineScale_iff x₀ hr, translateSet_smul_euclideanBall x₀ hr]

theorem setLIntegral_comp_affineScale_ball (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (ρ : ℝ)
    (g : Vec d → ENNReal) :
    ∫⁻ y in euclideanBall (0 : Vec d) ρ, g (r • y + x₀) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ x in euclideanBall x₀ (r * ρ), g x := by
  rw [setLIntegral_comp_affineScale x₀ hr, translateSet_smul_euclideanBall x₀ hr]

end DGNM

end PDE
