module

public import PDEFoundation.Sobolev.Trace.Chart.SurfaceBasic

/-!
# Surface measure on a chart cylinder

On the chart cylinder `φ.dom`, the surface measure `σ = boundarySurfaceMeasure Ω` is comparable
with the push-forward of Lebesgue measure on `B_r(c)` under the boundary parametrisation
`x' ↦ φ.map (x', 0)`, with constant `√(1 + L²)^n`.  Consequently `σ` is finite for a trace atlas.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The surface measure of a measurable set is the Euclidean Hausdorff measure of the Hilbert
image of its intersection with the frontier. -/
theorem boundarySurfaceMeasure_apply {t : Set (Vec (n + 1))} (ht : MeasurableSet t) :
    boundarySurfaceMeasure Ω t = (μHE[n] : Measure (HilbertVec (n + 1)))
      (Vec.toHilbertVec '' (t ∩ frontier Ω)) := by
  unfold boundarySurfaceMeasure
  rw [Measure.map_apply (show Measurable (HilbertVec.toVec (d := (n + 1))) from (MeasurableEquiv.toLp 2 (Vec (n + 1))).symm.measurable) ht,
    Measure.restrict_apply ((show Measurable (HilbertVec.toVec (d := (n + 1))) from (MeasurableEquiv.toLp 2 (Vec (n + 1))).symm.measurable) ht)]
  congr 1
  ext w
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨h1, x, hx, rfl⟩
    exact ⟨x, ⟨h1, hx⟩, rfl⟩
  · rintro ⟨x, ⟨h1, hx⟩, rfl⟩
    exact ⟨h1, x, hx, rfl⟩

namespace GraphChart

theorem measurable_boundaryMap (φ : GraphChart Ω) :
    Measurable fun x' : Vec n => φ.map (x', 0) :=
  ((contDiff_graphMap φ.γ_contDiff).continuous.comp
    (continuous_id.prodMk continuous_const)).measurable

private theorem surface_restrict_apply (φ : GraphChart Ω) {s : Set (Vec (n + 1))}
    (hs : MeasurableSet s) :
    (boundarySurfaceMeasure Ω).restrict φ.dom s = (μHE[n] : Measure (HilbertVec (n + 1)))
      (Vec.toHilbertVec '' ((fun x' => φ.map (x', 0)) ''
        ((fun x' => φ.map (x', 0)) ⁻¹' s ∩ euclideanBall φ.c φ.r))) := by
  rw [Measure.restrict_apply hs, boundarySurfaceMeasure_apply (hs.inter φ.isOpen_dom.measurableSet)]
  congr 2
  have hF : frontier Ω ∩ φ.dom = (fun x' => φ.map (x', 0)) '' euclideanBall φ.c φ.r := by
    rw [φ.frontier_inter_dom]
    ext w
    simp only [mem_image, mem_prod, mem_singleton_iff, Prod.exists]
    constructor
    · rintro ⟨x, t, ⟨hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, 0, ⟨hx, rfl⟩, rfl⟩
  calc s ∩ φ.dom ∩ frontier Ω = s ∩ (frontier Ω ∩ φ.dom) := by
        ext; simp only [mem_inter_iff]; tauto
    _ = _ := by
        rw [hF]
        exact (image_preimage_inter _ _ _).symm.trans (by rw [inter_comm]) |>.trans rfl

theorem map_le_surface (φ : GraphChart Ω) :
    Measure.map (fun x' => φ.map (x', 0)) (volume.restrict (euclideanBall φ.c φ.r)) ≤
      (boundarySurfaceMeasure Ω).restrict φ.dom := by
  refine Measure.le_iff.2 fun s hs => ?_
  have hA : MeasurableSet ((fun x' => φ.map (x', 0)) ⁻¹' s ∩ euclideanBall φ.c φ.r) :=
    (φ.measurable_boundaryMap hs).inter (measurableSet_euclideanBall _ _)
  rw [Measure.map_apply φ.measurable_boundaryMap hs, Measure.restrict_apply
    (φ.measurable_boundaryMap hs), surface_restrict_apply φ hs]
  exact φ.volume_le_hausdorff_graph hA

theorem surface_le_map (φ : GraphChart Ω) :
    (boundarySurfaceMeasure Ω).restrict φ.dom ≤
      ENNReal.ofReal (Real.sqrt (1 + φ.L ^ 2) ^ n) •
        Measure.map (fun x' => φ.map (x', 0)) (volume.restrict (euclideanBall φ.c φ.r)) := by
  refine Measure.le_iff.2 fun s hs => ?_
  have hA : MeasurableSet ((fun x' => φ.map (x', 0)) ⁻¹' s ∩ euclideanBall φ.c φ.r) :=
    (φ.measurable_boundaryMap hs).inter (measurableSet_euclideanBall _ _)
  rw [Measure.smul_apply, Measure.map_apply φ.measurable_boundaryMap hs, Measure.restrict_apply
    (φ.measurable_boundaryMap hs), surface_restrict_apply φ hs, smul_eq_mul]
  exact φ.hausdorff_graph_le_volume hA

end GraphChart

/-- The surface measure of a trace atlas is finite (boundedness of `Ω` is not needed: the atlas
cylinders already cover `∂Ω` by finitely many charts). -/
theorem boundarySurfaceMeasure_isFiniteMeasure (A : TraceAtlas Ω)
    (_hΩb : Bornology.IsBounded Ω) : IsFiniteMeasure (boundarySurfaceMeasure Ω) := by
  constructor
  have hcov : frontier Ω ⊆ ⋃ j, (A.chart j).dom := by
    intro x hx
    have hxV := A.frontier_subset hx
    have hsum := A.sum_eq_one x hxV
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    have : ∀ j, A.ζ j x = 0 := fun j => by
      by_contra h
      exact hnot j (A.ζ_tsupport j (subset_tsupport _ (Function.mem_support.2 h)))
    simp [this] at hsum
  have hU : MeasurableSet (⋃ j, (A.chart j).dom) :=
    MeasurableSet.iUnion fun j => (A.chart j).isOpen_dom.measurableSet
  have h1 : boundarySurfaceMeasure Ω univ = boundarySurfaceMeasure Ω (⋃ j, (A.chart j).dom) := by
    rw [boundarySurfaceMeasure_apply MeasurableSet.univ, boundarySurfaceMeasure_apply hU,
      univ_inter, inter_eq_right.2 hcov]
  rw [h1]
  refine lt_of_le_of_lt (measure_iUnion_fintype_le _ _) (ENNReal.sum_lt_top.2 fun j _ => ?_)
  have h2 : boundarySurfaceMeasure Ω (A.chart j).dom =
      (boundarySurfaceMeasure Ω).restrict (A.chart j).dom univ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [h2]
  refine lt_of_le_of_lt ((A.chart j).surface_le_map univ) ?_
  rw [Measure.smul_apply, Measure.map_apply (A.chart j).measurable_boundaryMap
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top _ (A.chart j).r_pos.le))

end PDE.TraceLane
