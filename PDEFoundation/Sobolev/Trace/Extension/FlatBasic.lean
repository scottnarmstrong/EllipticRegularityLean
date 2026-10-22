module

public import PDEFoundation.Sobolev.Trace.Chart.Surface
public import PDEFoundation.Sobolev.Trace.Chart.FactsTopology

/-!
# Basic facts for the flat pull-back of a cut-off boundary function

`flatPullback φ ζ g x' = ζ (Ψ₀ x') g (Ψ₀ x')` with `Ψ₀ x' = φ.map (x', 0)`.  It vanishes off the
chart ball `B = euclideanBall φ.c φ.r`, the cut-off `ζ` is bounded and Lipschitz for the Euclidean
distance, the support of `flatPullback` stays at positive distance from the complement of `B`, and
`Ψ₀` pushes Lebesgue measure on `B` below the surface measure.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Pull back of a cut-off boundary function to the flat chart. -/
noncomputable def flatPullback (φ : GraphChart Ω) (ζ g : Vec (n + 1) → ℝ) (x' : Vec n) : ℝ :=
  ζ (φ.map (x', 0)) * g (φ.map (x', 0))

namespace GraphChart

theorem map_zero_mem_dom_iff (φ : GraphChart Ω) (x' : Vec n) :
    φ.map (x', 0) ∈ φ.dom ↔ x' ∈ euclideanBall φ.c φ.r := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = (x', 0) := φ.homeo.injective hzx
    rw [this] at hz
    exact hz.1
  · intro hx
    exact ⟨(x', 0), ⟨hx, by simpa using φ.a_pos⟩, rfl⟩

theorem flatPullback_eq_zero_of_notMem (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ}
    (hζU : tsupport ζ ⊆ φ.dom) (g : Vec (n + 1) → ℝ) {x' : Vec n}
    (hx : x' ∉ euclideanBall φ.c φ.r) : flatPullback φ ζ g x' = 0 := by
  have h : φ.map (x', 0) ∉ tsupport ζ := fun h => hx ((φ.map_zero_mem_dom_iff x').1 (hζU h))
  simp [flatPullback, image_eq_zero_of_notMem_tsupport h]

theorem measurableSet_ball (φ : GraphChart Ω) : MeasurableSet (euclideanBall φ.c φ.r) :=
  measurableSet_euclideanBall _ _

instance (φ : GraphChart Ω) : IsFiniteMeasure (volume.restrict (euclideanBall φ.c φ.r)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top _ φ.r_pos.le)⟩

theorem mapBoundary_le_surface (φ : GraphChart Ω) :
    Measure.map (fun x' => φ.map (x', 0)) (volume.restrict (euclideanBall φ.c φ.r)) ≤
      boundarySurfaceMeasure Ω :=
  φ.map_le_surface.trans Measure.restrict_le_self

/-- Integrals over the chart ball of a boundary function are bounded by surface integrals. -/
theorem lintegral_boundaryMap_le (φ : GraphChart Ω) {f : Vec (n + 1) → ℝ≥0∞}
    (hf : AEMeasurable f (boundarySurfaceMeasure Ω)) :
    ∫⁻ x' in euclideanBall φ.c φ.r, f (φ.map (x', 0)) ≤ ∫⁻ x, f x ∂boundarySurfaceMeasure Ω := by
  rw [← lintegral_map' (hf.mono_measure φ.mapBoundary_le_surface)
    φ.measurable_boundaryMap.aemeasurable]
  exact lintegral_mono' φ.mapBoundary_le_surface le_rfl

/-- Double integrals over the chart ball of a boundary function are bounded by double surface
integrals. -/
theorem lintegral_boundaryMap_prod_le (φ : GraphChart Ω)
    {F : Vec (n + 1) → Vec (n + 1) → ℝ≥0∞} (hF : Measurable fun q : Vec (n + 1) × Vec (n + 1) =>
      F q.1 q.2) :
    ∫⁻ x' in euclideanBall φ.c φ.r, ∫⁻ y' in euclideanBall φ.c φ.r,
        F (φ.map (x', 0)) (φ.map (y', 0)) ≤
      ∫⁻ x, ∫⁻ y, F x y ∂boundarySurfaceMeasure Ω ∂boundarySurfaceMeasure Ω := by
  set ν := Measure.map (fun x' => φ.map (x', 0)) (volume.restrict (euclideanBall φ.c φ.r))
    with hν
  have hmeas := φ.measurable_boundaryMap
  have hle := φ.mapBoundary_le_surface
  have h1 : ∀ a : Vec (n + 1), ∫⁻ y' in euclideanBall φ.c φ.r, F a (φ.map (y', 0)) =
      ∫⁻ y, F a y ∂ν := fun a =>
    (lintegral_map (hF.comp measurable_prodMk_left) hmeas).symm
  simp_rw [h1]
  have h2 : Measurable fun x => ∫⁻ y, F x y ∂ν := hF.lintegral_prod_right'
  calc ∫⁻ x' in euclideanBall φ.c φ.r, (fun x => ∫⁻ y, F x y ∂ν) (φ.map (x', 0))
      = ∫⁻ x, ∫⁻ y, F x y ∂ν ∂ν := (lintegral_map h2 hmeas).symm
    _ ≤ ∫⁻ x, ∫⁻ y, F x y ∂boundarySurfaceMeasure Ω ∂ν :=
        lintegral_mono (fun x => lintegral_mono' hle le_rfl)
    _ ≤ _ := lintegral_mono' hle le_rfl

end GraphChart

/-- A continuous compactly supported function is bounded. -/
theorem exists_abs_le_of_hasCompactSupport {d : ℕ} {ζ : Vec d → ℝ} (hc : Continuous ζ)
    (hK : HasCompactSupport ζ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ X, |ζ X| ≤ M := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hK
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun X => by simpa using hC X⟩

/-- A `C¹` compactly supported function is Lipschitz for the Euclidean distance. -/
theorem exists_lipschitz_of_contDiff {d : ℕ} {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hK : HasCompactSupport ζ) :
    ∃ Lz : ℝ, 0 ≤ Lz ∧ ∀ X Y, |ζ X - ζ Y| ≤ Lz * vecEuclideanNorm (X - Y) := by
  obtain ⟨K, hK'⟩ := hζ.lipschitzWith_of_hasCompactSupport hK (by norm_num)
  refine ⟨K, K.2, fun X Y => ?_⟩
  have h := hK'.dist_le_mul X Y
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) K.2)

namespace GraphChart

/-- The support of the cut-off stays at a positive distance from the complement of the chart
ball. -/
theorem exists_delta (φ : GraphChart Ω) {ζ : Vec (n + 1) → ℝ} (hζK : HasCompactSupport ζ)
    (hζU : tsupport ζ ⊆ φ.dom) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x' y' : Vec n, φ.map (x', 0) ∈ tsupport ζ →
      vecEuclideanNorm (x' - y') < δ → y' ∈ euclideanBall φ.c φ.r := by
  set K' : Set (Vec n) := {x' | φ.map (x', 0) ∈ tsupport ζ} with hK'
  have hcont : Continuous fun x' : Vec n => φ.map (x', 0) := by
    have := φ.homeo.continuous
    exact this.comp (continuous_id.prodMk continuous_const)
  have hclosed : IsClosed K' := (isClosed_tsupport ζ).preimage hcont
  have hcomp : IsCompact K' := by
    have h1 : IsCompact (φ.homeo ⁻¹' tsupport ζ) := φ.homeo.isCompact_preimage.2 hζK
    refine (h1.image continuous_fst).of_isClosed_subset hclosed (fun x' hx' => ?_)
    exact ⟨(x', 0), hx', rfl⟩
  have hsub : K' ⊆ euclideanBall φ.c φ.r := fun x' hx' =>
    (φ.map_zero_mem_dom_iff x').1 (hζU hx')
  obtain ⟨δ, hδ, hth⟩ := hcomp.exists_thickening_subset_open (isOpen_euclideanBall φ.c φ.r) hsub
  refine ⟨δ, hδ, fun x' y' hx' hxy => hth ?_⟩
  refine Metric.mem_thickening_iff.2 ⟨x', hx', ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt ((norm_le_vecEuclideanNorm _).trans_eq (vecEuclideanNorm_sub_comm _ _)) hxy

end GraphChart

end PDE.TraceLane
