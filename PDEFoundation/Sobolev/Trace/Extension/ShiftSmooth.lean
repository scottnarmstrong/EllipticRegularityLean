module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftBasic
public import PDEFoundation.Sobolev.Trace.Smooth.Pullback

/-!
# Shifted extensions are `C¹` near `Ω̄`

For `s ≥ 0`, each summand `ηⱼ · (modelExt n gⱼ)(φⱼ⁻¹ x + (0, s))` is `C¹` at every `x` for which
`φⱼ⁻¹ x` has `t + s > 0` whenever `x ∈ tsupport ηⱼ`.  For `s > 0` this holds on `Ω̄`; for `s = 0`
it holds on `Ω`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

namespace GraphChart

theorem inv_map (φ : GraphChart Ω) (z : Vec n × ℝ) : φ.inv (φ.map z) = z :=
  graphMapInv_graphMap φ.sgn_sq z

theorem map_inv (φ : GraphChart Ω) (x : Vec (n + 1)) : φ.map (φ.inv x) = x :=
  graphMap_graphMapInv φ.sgn_sq x

theorem contDiff_inv (φ : GraphChart Ω) : ContDiff ℝ 1 φ.inv :=
  contDiff_graphMapInv φ.γ_contDiff

theorem exists_eq_map_of_mem_dom (φ : GraphChart Ω) {x : Vec (n + 1)} (hx : x ∈ φ.dom) :
    ∃ z, x = φ.map z ∧ z.1 ∈ euclideanBall φ.c φ.r ∧ z.2 ∈ Ioo (-φ.a) φ.a := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨z, rfl, hz.1, hz.2⟩

theorem inv_snd_nonneg_of_mem_closure (φ : GraphChart Ω) {x : Vec (n + 1)}
    (hx : x ∈ closure Ω) (hd : x ∈ φ.dom) : 0 ≤ (φ.inv x).2 := by
  have h : x ∈ φ.map '' (euclideanBall φ.c φ.r ×ˢ Ico 0 φ.a) := by
    rw [← φ.closure_inter_dom]; exact ⟨hx, hd⟩
  obtain ⟨z, hz, rfl⟩ := h
  rw [φ.inv_map]
  exact hz.2.1

theorem inv_snd_pos_of_mem (φ : GraphChart Ω) {x : Vec (n + 1)}
    (hx : x ∈ Ω) (hd : x ∈ φ.dom) : 0 < (φ.inv x).2 := by
  have h : x ∈ φ.map '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := by
    have := φ.inter_eq
    change Ω ∩ φ.dom = φ.map '' _ at this
    rw [← this]; exact ⟨hx, hd⟩
  obtain ⟨z, hz, rfl⟩ := h
  rw [φ.inv_map]
  exact hz.2.1

end GraphChart

theorem ExtData.locallyIntegrable_flat (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    LocallyIntegrable (D.flat j g) volume :=
  (D.flat_memLp j hp hg).locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp.le)

/-- A summand is `C¹` where the shifted chart coordinate stays in the open half-space. -/
theorem ExtData.term_contDiffAt (D : ExtData Ω) (j : Fin D.A.N) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {s : ℝ} {x : Vec (n + 1)}
    (hx : x ∈ tsupport (D.η j) → 0 < ((D.A.chart j).inv x).2 + s) :
    ContDiffAt ℝ 1 (D.term j s g) x := by
  by_cases hxs : x ∈ tsupport (D.η j)
  · have hE := contDiffOn_modelExt (D.locallyIntegrable_flat j hp hg)
    have hmem : (D.A.chart j).inv x + ((0 : Vec n), s) ∈ upperHalf n := by
      rw [mem_upperHalf]; simpa using hx hxs
    have hF : ContDiffAt ℝ 1 (modelExt n (D.flat j g)) ((D.A.chart j).inv x + ((0 : Vec n), s)) :=
      hE.contDiffAt ((isOpen_upperHalf n).mem_nhds hmem)
    have hlin : ContDiff ℝ 1 fun y => (D.A.chart j).inv y + ((0 : Vec n), s) :=
      (D.A.chart j).contDiff_inv.add contDiff_const
    have hF' : ContDiffAt ℝ 1 (fun y => modelExt n (D.flat j g)
        ((D.A.chart j).inv y + ((0 : Vec n), s))) x :=
      ContDiffAt.comp (g := modelExt n (D.flat j g)) x hF hlin.contDiffAt
    exact ((D.η_smooth j).of_le (by exact_mod_cast le_top)).contDiffAt.mul hF'
  · have hev : D.term j s g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport (D.η j)).isOpen_compl.mem_nhds hxs] with y hy
      simp [ExtData.term, image_eq_zero_of_notMem_tsupport hy]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

theorem ExtData.shift_contDiffAt (D : ExtData Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {s : ℝ} {x : Vec (n + 1)}
    (hx : ∀ j, x ∈ tsupport (D.η j) → 0 < ((D.A.chart j).inv x).2 + s) :
    ContDiffAt ℝ 1 (D.shift s g) x := by
  rw [D.shift_eq_sum_term]
  exact ContDiffAt.sum fun j _ => D.term_contDiffAt j hp hg (hx j)

theorem ExtData.pos_of_mem_closure (D : ExtData Ω) {x : Vec (n + 1)} (hx : x ∈ closure Ω)
    {τ : ℝ} (hτ : 0 < τ) (j : Fin D.A.N) (hj : x ∈ tsupport (D.η j)) :
    0 < ((D.A.chart j).inv x).2 + τ := by
  have := (D.A.chart j).inv_snd_nonneg_of_mem_closure hx (D.η_tsupport j hj)
  linarith

theorem ExtData.pos_of_mem (D : ExtData Ω) {x : Vec (n + 1)} (hx : x ∈ Ω)
    (j : Fin D.A.N) (hj : x ∈ tsupport (D.η j)) :
    0 < ((D.A.chart j).inv x).2 + 0 := by
  have := (D.A.chart j).inv_snd_pos_of_mem hx (D.η_tsupport j hj)
  linarith

theorem ExtData.shift_contDiffOn (D : ExtData Ω) {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ}
    (hg : IsBesov Ω (1 - 1 / p) p g) {τ : ℝ} (hτ : 0 < τ) :
    ContDiffOn ℝ 1 (D.shift τ g) (closure Ω) := fun _ hx =>
  (D.shift_contDiffAt hp hg fun j hj => D.pos_of_mem_closure hx hτ j hj).contDiffWithinAt

end PDE.TraceLane
