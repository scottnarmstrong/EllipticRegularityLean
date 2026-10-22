module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Measure.DilationLp
public import PDEFoundation.Geometry.EuclideanBall.Basic

/-!
# Change of variables under `y ↦ ρ • y + x₀` for restricted volume

Almost-everywhere statements, and `L²` norms, transfer between the unit-scale
picture on `euclideanBall 0 s` and the picture on `euclideanBall x₀ (ρ * s)`.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMHolder

open PDE MeasureTheory

variable {d : ℕ}

theorem smul_euclideanBall_zero {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    ρ • euclideanBall (0 : Vec d) s = euclideanBall (0 : Vec d) (ρ * s) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
  change euclideanSqDist (ρ⁻¹ • x) 0 < s ^ 2 ↔ euclideanSqDist x 0 < (ρ * s) ^ 2
  have h := euclideanSqDist_smul_smul (d := d) ρ⁻¹ x 0
  rw [smul_zero] at h
  rw [h, mul_pow]
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  constructor
  · intro hlt
    have := mul_lt_mul_of_pos_left hlt hρ2
    calc euclideanSqDist x 0 = ρ ^ 2 * ((ρ⁻¹) ^ 2 * euclideanSqDist x 0) := by
          field_simp
      _ < ρ ^ 2 * s ^ 2 := this
  · intro hlt
    have : (ρ⁻¹) ^ 2 * euclideanSqDist x 0 < (ρ⁻¹) ^ 2 * (ρ ^ 2 * s ^ 2) :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    calc (ρ⁻¹) ^ 2 * euclideanSqDist x 0 < (ρ⁻¹) ^ 2 * (ρ ^ 2 * s ^ 2) := this
      _ = s ^ 2 := by field_simp

theorem translateSet_smul_euclideanBall {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) (s : ℝ) :
    translateSet x₀ (ρ • euclideanBall (0 : Vec d) s) = euclideanBall x₀ (ρ * s) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, smul_euclideanBall_zero hρ]
  change euclideanSqDist (x - x₀) 0 < (ρ * s) ^ 2 ↔ euclideanSqDist x x₀ < (ρ * s) ^ 2
  simp [euclideanSqDist]

/-- The affine map `y ↦ ρ • y + x₀` pushes restricted volume on `S` to a constant
multiple of restricted volume on `translateSet x₀ (ρ • S)`. -/
theorem map_affine_volumeOn {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) (S : Set (Vec d)) :
    Measure.map (fun y : Vec d => ρ • y + x₀) (volumeOn S) =
      ENNReal.ofReal ((ρ ^ d)⁻¹) • volumeOn (translateSet x₀ (ρ • S)) := by
  have h1 := map_smul_volumeOn_of_pos (d := d) hρ S
  have hmeas1 : Measurable (fun y : Vec d => ρ • y) := measurable_const_smul _
  have hmeas2 : Measurable (fun z : Vec d => z + x₀) := measurable_add_const _
  have hcomp : (fun y : Vec d => ρ • y + x₀) = (fun z : Vec d => z + x₀) ∘ (fun y : Vec d => ρ • y) := rfl
  rw [hcomp, ← Measure.map_map hmeas2 hmeas1, h1, Measure.map_smul]
  congr 1
  exact (measurePreserving_addRight_restrict_translateSet x₀ (ρ • S)).map_eq
  all_goals exact hmeas2.aemeasurable

theorem measurableEmbedding_affine {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) :
    MeasurableEmbedding (fun y : Vec d => ρ • y + x₀) := by
  have h1 : MeasurableEmbedding (fun y : Vec d => ρ • y) := by
    let u : ℝˣ := (isUnit_iff_ne_zero.2 hρ.ne').unit
    have hu : (u : ℝ) = ρ := (isUnit_iff_ne_zero.2 hρ.ne').unit_spec
    simpa [hu] using! (Homeomorph.smul u : Vec d ≃ₜ Vec d).measurableEmbedding
  exact (Homeomorph.addRight x₀).measurableEmbedding.comp h1

/-- Almost-everywhere statements transfer under the affine change of variables. -/
theorem ae_affine_iff {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) (S : Set (Vec d)) (P : Vec d → Prop) :
    (∀ᵐ y ∂volumeOn S, P (ρ • y + x₀)) ↔
      ∀ᵐ x ∂volumeOn (translateSet x₀ (ρ • S)), P x := by
  have hc : ENNReal.ofReal ((ρ ^ d)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hρ d))).ne'
  rw [← (measurableEmbedding_affine hρ x₀).ae_map_iff, map_affine_volumeOn hρ x₀ S]
  simp [ae_iff, hc]

/-- Almost-everywhere statements transfer between `euclideanBall 0 s` and
`euclideanBall x₀ (ρ * s)`. -/
theorem ae_affine_ball_iff {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) (s : ℝ) (P : Vec d → Prop) :
    (∀ᵐ y ∂volumeOn (euclideanBall (0 : Vec d) s), P (ρ • y + x₀)) ↔
      ∀ᵐ x ∂volumeOn (euclideanBall x₀ (ρ * s)), P x := by
  rw [ae_affine_iff hρ x₀, translateSet_smul_euclideanBall hρ]

/-- Exact `L²` scaling under the affine change of variables. -/
theorem eLpNorm_comp_affine_ball {ρ : ℝ} (hρ : 0 < ρ) (x₀ : Vec d) (s : ℝ) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volumeOn (euclideanBall x₀ (ρ * s)))) :
    eLpNorm (fun y => f (ρ • y + x₀)) 2 (volumeOn (euclideanBall (0 : Vec d) s)) =
      ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
        eLpNorm f 2 (volumeOn (euclideanBall x₀ (ρ * s))) := by
  have hc : ENNReal.ofReal ((ρ ^ d)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos hρ d))).ne'
  have hmap := map_affine_volumeOn hρ x₀ (euclideanBall (0 : Vec d) s)
  rw [translateSet_smul_euclideanBall hρ] at hmap
  have hf' : AEStronglyMeasurable f
      (Measure.map (fun y : Vec d => ρ • y + x₀) (volumeOn (euclideanBall (0 : Vec d) s))) := by
    rw [hmap]; exact hf.smul_measure _
  have := eLpNorm_map_measure (p := 2) hf'
    (measurableEmbedding_affine hρ x₀).measurable.aemeasurable
  rw [Function.comp_def] at this
  rw [← this, hmap, eLpNorm_smul_measure_of_ne_zero hc]
  simp

end PDE.DGNMHolder
