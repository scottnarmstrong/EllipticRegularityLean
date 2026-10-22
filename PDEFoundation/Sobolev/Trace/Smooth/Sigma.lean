module

public import PDEFoundation.Sobolev.Trace.Chart.Surface

/-!
# Surface integrals on a chart cylinder

On the chart cylinder, integrals against the surface measure `σ` are bounded by
`√(1+L²)^n` times integrals over the parameter domain `x' ∈ Vec n` along `x' ↦ Ψ(x', 0)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The comparison constant of the surface measure on a chart. -/
noncomputable def surfConst (φ : GraphChart Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (1 + φ.L ^ 2) ^ n)

theorem surfConst_ne_top (φ : GraphChart Ω) : surfConst φ ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Single integrals against `σ` of functions supported in the chart cylinder. -/
theorem lintegral_sigma_le (φ : GraphChart Ω) (h : Vec (n + 1) → ℝ≥0∞)
    (hsupp : ∀ x ∉ φ.dom, h x = 0) :
    ∫⁻ x, h x ∂boundarySurfaceMeasure Ω ≤
      surfConst φ * ∫⁻ x', h (φ.map (x', 0)) := by
  have h1 : ∫⁻ x, h x ∂boundarySurfaceMeasure Ω =
      ∫⁻ x, h x ∂(boundarySurfaceMeasure Ω).restrict φ.dom :=
    (setLIntegral_eq_of_support_subset (fun x hx => by
      by_contra hxd; exact hx (hsupp x hxd))).symm
  rw [h1]
  calc _ ≤ ∫⁻ x, h x ∂(surfConst φ •
        Measure.map (fun x' => φ.map (x', 0)) (volume.restrict (euclideanBall φ.c φ.r))) :=
        lintegral_mono' φ.surface_le_map le_rfl
    _ = surfConst φ * ∫⁻ x, h x ∂Measure.map (fun x' => φ.map (x', 0))
          (volume.restrict (euclideanBall φ.c φ.r)) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ surfConst φ * ∫⁻ x', h (φ.map (x', 0)) ∂(volume.restrict (euclideanBall φ.c φ.r)) := by
        gcongr
        exact lintegral_map_le _ φ.measurable_boundaryMap.aemeasurable
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

/-- Iterated integrals against `σ|dom` of the chart cylinder. -/
theorem lintegral_sigma_iter_le (φ : GraphChart Ω) (G : Vec (n + 1) → Vec (n + 1) → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, G x y ∂(boundarySurfaceMeasure Ω).restrict φ.dom
        ∂(boundarySurfaceMeasure Ω).restrict φ.dom ≤
      surfConst φ * (surfConst φ * ∫⁻ x', ∫⁻ y', G (φ.map (x', 0)) (φ.map (y', 0))) := by
  set m : Measure (Vec (n + 1)) := Measure.map (fun x' => φ.map (x', 0))
    (volume.restrict (euclideanBall φ.c φ.r)) with hm
  have hmap : ∀ F : Vec (n + 1) → ℝ≥0∞,
      ∫⁻ x, F x ∂m ≤ ∫⁻ x', F (φ.map (x', 0)) := fun F =>
    (lintegral_map_le F φ.measurable_boundaryMap.aemeasurable).trans
      (lintegral_mono' Measure.restrict_le_self le_rfl)
  have hc := surfConst_ne_top φ
  calc _ ≤ ∫⁻ x, ∫⁻ y, G x y ∂(surfConst φ • m) ∂(surfConst φ • m) :=
        lintegral_mono' φ.surface_le_map fun x => lintegral_mono' φ.surface_le_map le_rfl
    _ = surfConst φ * (surfConst φ * ∫⁻ x, ∫⁻ y, G x y ∂m ∂m) := by
        simp_rw [lintegral_smul_measure, smul_eq_mul]
        rw [lintegral_const_mul' _ _ hc]
    _ ≤ surfConst φ * (surfConst φ * ∫⁻ x', ∫⁻ y, G (φ.map (x', 0)) y ∂m) := by
        gcongr
        exact hmap (fun x => ∫⁻ y, G x y ∂m)
    _ ≤ surfConst φ * (surfConst φ * ∫⁻ x', ∫⁻ y', G (φ.map (x', 0)) (φ.map (y', 0))) := by
        gcongr with x'
        exact hmap (fun y => G (φ.map (x', 0)) y)

end PDE.TraceLane
