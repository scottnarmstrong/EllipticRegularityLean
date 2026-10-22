module

public import PDEFoundation.Sobolev.Trace.Extension.ExtLinear
public import PDEFoundation.Sobolev.Trace.Model.Ext
import PDEFoundation.Sobolev.Trace.Smooth.Pullback

/-!
# The extension is `C¹` on `Ω`

Near a point of `Ω` inside the cylinder of chart `j`, the inverse chart maps into the open
half-space, where `modelExt` is `C¹`; away from the support of the cutoff `ηⱼ` the `j`-th summand
vanishes identically nearby.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Points of `Ω` in the chart cylinder are mapped by the inverse chart into the open half-space. -/
theorem ext_inv_mem_upperHalf (φ : GraphChart Ω) {y : Vec (n + 1)} (hy : y ∈ Ω)
    (hd : y ∈ φ.dom) : φ.inv y ∈ upperHalf n := by
  have h : y ∈ Ω ∩ graphMap φ.i φ.γ φ.sgn '' (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) := ⟨hy, hd⟩
  rw [φ.inter_eq] at h
  obtain ⟨z, hz, rfl⟩ := h
  have : φ.inv (graphMap φ.i φ.γ φ.sgn z) = z := graphMapInv_graphMap φ.sgn_sq z
  rw [this]
  exact ⟨mem_univ _, hz.2.1⟩

theorem GraphChart.contDiff_inv (φ : GraphChart Ω) : ContDiff ℝ 1 φ.inv :=
  contDiff_graphMapInv φ.γ_contDiff

/-- A cut-off composition with the inverse chart of a function which is `C¹` on the open
half-space is `C¹` on `Ω`. -/
theorem ExtData.contDiffOn_term (D : ExtData Ω) (j : Fin D.A.N) {F : Vec n × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (upperHalf n)) :
    ContDiffOn ℝ 1 (fun x => D.η j x * F ((D.A.chart j).inv x)) Ω := by
  intro x hx
  by_cases hxs : x ∈ tsupport (D.η j)
  · have hxd : x ∈ (D.A.chart j).dom := D.η_tsupport j hxs
    set W : Set (Vec (n + 1)) := Ω ∩ (D.A.chart j).dom with hW
    have hmaps : MapsTo (D.A.chart j).inv W (upperHalf n) := fun y hy =>
      ext_inv_mem_upperHalf _ hy.1 hy.2
    have h1 : ContDiffOn ℝ 1 (fun y => D.η j y * F ((D.A.chart j).inv y)) W :=
      (D.contDiff_η j).contDiffOn.mul (hF.comp (D.A.chart j).contDiff_inv.contDiffOn hmaps)
    have hWo : IsOpen W := by
      have : W = (D.A.chart j).homeo '' (euclideanBall (D.A.chart j).c (D.A.chart j).r ×ˢ
          Ioo 0 (D.A.chart j).a) := (D.A.chart j).inter_eq
      rw [this]
      exact (D.A.chart j).homeo.isOpenMap _ ((isOpen_euclideanBall _ _).prod isOpen_Ioo)
    exact (h1.contDiffAt (hWo.mem_nhds ⟨hx, hxd⟩)).contDiffWithinAt
  · have hev : (fun y => D.η j y * F ((D.A.chart j).inv y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport (D.η j)).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt

/-- The extension is `C¹` on `Ω`. -/
theorem ExtData.ext_contDiffOn (D : ExtData Ω) {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) : ContDiffOn ℝ 1 (D.ext g) Ω := by
  unfold ExtData.ext
  exact ContDiffOn.sum fun j _ =>
    D.contDiffOn_term j (modelExt_contDiffOn hp _ (D.memLp_flat j hp hg))

end PDE.TraceLane
