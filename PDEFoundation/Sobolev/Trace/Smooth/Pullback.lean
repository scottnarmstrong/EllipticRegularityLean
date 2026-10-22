module

public import PDEFoundation.Sobolev.Trace.Smooth.Calculus
public import PDEFoundation.Sobolev.Trace.Model.Defs
public import PDEFoundation.Sobolev.Trace.Assembly.Basic

/-!
# The localised pullback `v = (ζ u) ∘ Ψ` on the half-space

For a graph chart `φ`, a cutoff `ζ` with `tsupport ζ ⊆ φ.dom`, and `u ∈ C¹(Ω̄)`, the function
`v(x', t) = ζ(Ψ(x', t)) u(Ψ(x', t))` is `C¹` on the closed half-space, has compact support, and
vanishes near every point of the open half-space whose image is outside `Ω`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The localised pullback `v(z) = ζ(Ψ z) u(Ψ z)`. -/
noncomputable def pullback (φ : GraphChart Ω) (ζ u : Vec (n + 1) → ℝ) (z : Vec n × ℝ) : ℝ :=
  ζ (φ.map z) * u (φ.map z)

namespace GraphChart

theorem map_injective (φ : GraphChart Ω) : Function.Injective φ.map := φ.homeo.injective

theorem continuous_map (φ : GraphChart Ω) : Continuous φ.map := φ.homeo.continuous

theorem contDiff_map (φ : GraphChart Ω) : ContDiff ℝ 1 φ.map :=
  contDiff_graphMap φ.γ_contDiff

theorem map_mem_dom_iff (φ : GraphChart Ω) (z : Vec n × ℝ) :
    φ.map z ∈ φ.dom ↔ z.1 ∈ euclideanBall φ.c φ.r ∧ z.2 ∈ Ioo (-φ.a) φ.a := by
  have := φ.map_injective.mem_set_image (a := z)
    (s := euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a)
  simpa [GraphChart.dom] using this

theorem map_mem_of_mem_dom_of_pos (φ : GraphChart Ω) {z : Vec n × ℝ} (hz : 0 < z.2)
    (hd : φ.map z ∈ φ.dom) : φ.map z ∈ Ω := by
  rw [map_mem_dom_iff] at hd
  have h1 : φ.map z ∈ graphMap φ.i φ.γ φ.sgn '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) :=
    ⟨z, ⟨hd.1, hz, hd.2.2⟩, rfl⟩
  rw [← φ.inter_eq] at h1
  exact h1.1

theorem map_mem_closure_of_mem_dom_of_nonneg (φ : GraphChart Ω) {z : Vec n × ℝ} (hz : 0 ≤ z.2)
    (hd : φ.map z ∈ φ.dom) : φ.map z ∈ closure Ω := by
  have hd' := (map_mem_dom_iff φ z).1 hd
  have h1 : φ.map z ∈ φ.map '' (euclideanBall φ.c φ.r ×ˢ Ico 0 φ.a) :=
    ⟨z, ⟨hd'.1, hz, hd'.2.2⟩, rfl⟩
  rw [← φ.closure_inter_dom] at h1
  exact h1.1

end GraphChart

variable (φ : GraphChart Ω) {ζ u : Vec (n + 1) → ℝ}

/-- The pullback is `C¹` on the closed half-space. -/
theorem contDiffOn_pullback (hζ : ContDiff ℝ 1 ζ) (hts : tsupport ζ ⊆ φ.dom)
    (hu : ContDiffOn ℝ 1 u (closure Ω)) : ContDiffOn ℝ 1 (pullback φ ζ u) (closedUpperHalf n) := by
  intro z hz
  by_cases hzs : φ.map z ∈ tsupport ζ
  · have hdom := hts hzs
    set T : Set (Vec n × ℝ) := closedUpperHalf n ∩ φ.map ⁻¹' φ.dom with hT
    have hmaps : MapsTo φ.map T (closure Ω) := fun w hw =>
      φ.map_mem_closure_of_mem_dom_of_nonneg (by simpa [closedUpperHalf] using hw.1) hw.2
    have h1 : ContDiffOn ℝ 1 (fun w => ζ (φ.map w) * u (φ.map w)) T := by
      have h2 : ContDiffOn ℝ 1 (fun y => ζ y * u y) (closure Ω) := hζ.contDiffOn.mul hu
      exact h2.comp φ.contDiff_map.contDiffOn hmaps
    have hzT : z ∈ T := ⟨hz, hdom |> fun h => by simpa using h⟩
    refine (h1 z hzT).mono_of_mem_nhdsWithin ?_
    exact Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
      ((φ.isOpen_dom.preimage φ.continuous_map).mem_nhds (by simpa using hdom)))
  · have hev : pullback φ ζ u =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      have hopen : IsOpen (φ.map ⁻¹' (tsupport ζ)ᶜ) :=
        (isClosed_tsupport ζ).isOpen_compl.preimage φ.continuous_map
      filter_upwards [hopen.mem_nhds hzs] with w hw
      simp [pullback, image_eq_zero_of_notMem_tsupport hw]
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev).contDiffWithinAt

/-- The pullback has compact support. -/
theorem exists_compact_pullback (hζc : HasCompactSupport ζ) (u : Vec (n + 1) → ℝ) :
    ∃ K : Set (Vec n × ℝ), IsCompact K ∧ ∀ z ∉ K, pullback φ ζ u z = 0 := by
  refine ⟨φ.homeo ⁻¹' tsupport ζ, (φ.homeo.isCompact_preimage).2 hζc, fun z hz => ?_⟩
  have : φ.map z ∉ tsupport ζ := hz
  simp [pullback, image_eq_zero_of_notMem_tsupport this]

/-- At a point of the open half-space whose image is outside `Ω`, the pullback vanishes nearby. -/
theorem pullback_eventuallyEq_zero (hts : tsupport ζ ⊆ φ.dom) {z : Vec n × ℝ} (hz : 0 < z.2)
    (hzΩ : φ.map z ∉ Ω) : pullback φ ζ u =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hzs : φ.map z ∉ tsupport ζ := fun h => hzΩ (φ.map_mem_of_mem_dom_of_pos hz (hts h))
  have hopen : IsOpen (φ.map ⁻¹' (tsupport ζ)ᶜ) :=
    (isClosed_tsupport ζ).isOpen_compl.preimage φ.continuous_map
  filter_upwards [hopen.mem_nhds hzs] with w hw
  simp [pullback, image_eq_zero_of_notMem_tsupport hw]

end PDE.TraceLane
