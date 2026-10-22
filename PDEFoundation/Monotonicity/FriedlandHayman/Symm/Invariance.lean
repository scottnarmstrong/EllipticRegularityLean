module

public import PDEFoundation.Monotonicity.Core.BridgeSphere
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Friedland--Hayman: orthogonal invariance of the sphere measure

The unit sphere `Sph D` of `HilbertVec D` with its surface measure `sphMeasure D`, the action
`sphMap L` of a linear isometry on the sphere, the invariance of the surface measure under
`sphMap L`, the nullity of great spheres, and the hyperplane reflection `reflection' u`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Pointwise

namespace PDE.FHLane

noncomputable section

/-- The unit sphere of `HilbertVec D` and its surface measure. -/
abbrev Sph (D : ℕ) := Metric.sphere (0 : HilbertVec D) 1

/-- The surface measure on the unit sphere. -/
abbrev sphMeasure (D : ℕ) : MeasureTheory.Measure (Sph D) :=
  (MeasureTheory.volume : MeasureTheory.Measure (HilbertVec D)).toSphere


variable {D : ℕ}

/-- The action of a linear isometry equivalence on the unit sphere. -/
def sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) : Sph D → Sph D :=
  fun x => ⟨L x, by simp⟩

@[simp] theorem coe_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) (x : Sph D) :
    ((sphMap L x : Sph D) : HilbertVec D) = L x := rfl

theorem continuous_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) : Continuous (sphMap L) :=
  Continuous.subtype_mk (L.continuous.comp continuous_subtype_val) _

theorem sphMap_symm_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) (x : Sph D) :
    sphMap L.symm (sphMap L x) = x := by
  apply Subtype.ext; simp

theorem sphMap_sphMap_symm (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) (x : Sph D) :
    sphMap L (sphMap L.symm x) = x := by
  apply Subtype.ext; simp

theorem sphMeasure_preimage_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) {s : Set (Sph D)}
    (hs : MeasurableSet s) : sphMeasure D (sphMap L ⁻¹' s) = sphMeasure D s := by
  have hs' : MeasurableSet (sphMap L ⁻¹' s) := (continuous_sphMap L).measurable hs
  rw [Measure.toSphere_apply' _ hs', Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Ioo (0 : ℝ) 1 • (((↑) : Sph D → HilbertVec D) '' (sphMap L ⁻¹' s)) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • (((↑) : Sph D → HilbertVec D) '' s)) := by
    ext z
    simp only [mem_preimage]
    constructor
    · rintro ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨sphMap L x, hx, rfl⟩, by simp⟩
    · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, h⟩
      refine ⟨r, hr, _, ⟨sphMap L.symm y, ?_, rfl⟩, ?_⟩
      · simpa [sphMap_sphMap_symm] using hy
      · apply L.injective
        simpa using h
  rw [hcone]
  exact (LinearIsometryEquiv.measurePreserving L).measure_preimage_emb
    L.toHomeomorph.measurableEmbedding _

/-- F4-0: linear isometries preserve the sphere measure. -/
theorem measurePreserving_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) :
    MeasurePreserving (sphMap L) (sphMeasure D) (sphMeasure D) :=
  ⟨(continuous_sphMap L).measurable, Measure.ext fun s hs => by
    rw [Measure.map_apply (continuous_sphMap L).measurable hs, sphMeasure_preimage_sphMap L hs]⟩

theorem integrable_comp_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) {G : Sph D → ℝ}
    (hG : Integrable G (sphMeasure D)) : Integrable (fun x => G (sphMap L x)) (sphMeasure D) := by
  have := (measurePreserving_sphMap L).integrable_comp_of_integrable hG
  exact this

theorem integral_comp_sphMap (L : HilbertVec D ≃ₗᵢ[ℝ] HilbertVec D) {G : Sph D → ℝ}
    (hG : AEStronglyMeasurable G (sphMeasure D)) :
    ∫ x, G (sphMap L x) ∂(sphMeasure D) = ∫ x, G x ∂(sphMeasure D) := by
  have h := integral_map (measurePreserving_sphMap L).measurable.aemeasurable
    (by rwa [(measurePreserving_sphMap L).map_eq])
  rw [(measurePreserving_sphMap L).map_eq] at h
  exact h.symm

/-- Great spheres are null. -/
theorem sphMeasure_inner_eq_zero {u : HilbertVec D} (hu : u ≠ 0) :
    sphMeasure D {x | inner ℝ (x : HilbertVec D) u = 0} = 0 := by
  have hm : MeasurableSet {x : Sph D | inner ℝ (x : HilbertVec D) u = 0} :=
    (isClosed_eq (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  rw [Measure.toSphere_apply' _ hm]
  set K : Submodule ℝ (HilbertVec D) := LinearMap.ker (innerₛₗ ℝ u) with hK
  have hKtop : K ≠ ⊤ := by
    intro h
    have : u ∈ K := h ▸ Submodule.mem_top
    simp [hK, hu] at this
  have hsub : Ioo (0 : ℝ) 1 • (((↑) : Sph D → HilbertVec D) '' {x | inner ℝ (x : HilbertVec D) u = 0})
      ⊆ (K : Set (HilbertVec D)) := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, hK, LinearMap.mem_ker, innerₛₗ_apply_apply] at hx ⊢
    rw [inner_smul_right, real_inner_comm, hx, mul_zero]
  have : (volume : Measure (HilbertVec D)) K = 0 := Measure.addHaar_submodule _ K hKtop
  simp [measure_mono_null hsub this]

end

end PDE.FHLane
