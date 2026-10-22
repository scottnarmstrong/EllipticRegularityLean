module

public import PDEFoundation.Sobolev.Trace.Chart.FactsTopology

/-!
# Inward translation of a graph chart

For a graph chart `φ` with the direction `e = sgn • basisVec i`, the chart map satisfies
`Ψ (x', t + τ) = Ψ (x', t) + τ • e`, and consequently, for a compact set `K` in the chart
cylinder and small `τ > 0`, every point of `closure Ω` translated by `τ • e` either lies in `Ω` or
is outside `K` (`chart_translate_cover`).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The inward direction of a chart. -/
def GraphChart.dir (φ : GraphChart Ω) : Vec (n + 1) := φ.sgn • basisVec φ.i

theorem graphMap_add_right {i : Fin (n + 1)} {γ : Vec n → ℝ} {sgn : ℝ} (x' : Vec n) (t τ : ℝ) :
    graphMap i γ sgn (x', t + τ) = graphMap i γ sgn (x', t) + τ • (sgn • basisVec i) := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · simp only [graphMap, Fin.insertNth_apply_same, Pi.add_apply, Pi.smul_apply, basisVec_apply,
      smul_eq_mul, ite_true]
    ring
  · intro k
    simp [graphMap, Fin.insertNth_apply_succAbove, basisVec_apply,
      Fin.succAbove_ne i k]

/-- Small inward translates of `closure Ω` stay in `Ω` wherever they meet a compact set inside the
chart cylinder. -/
theorem chart_translate_cover (φ : GraphChart Ω) {K : Set (Vec (n + 1))} (hK : IsCompact K)
    (hKd : K ⊆ φ.dom) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ < τ₀ → ∀ x ∈ closure Ω,
      x + τ • φ.dir ∈ Ω ∪ Kᶜ := by
  obtain ⟨η, hη, hηd⟩ := hK.exists_cthickening_subset_open φ.isOpen_dom hKd
  have hpos : 0 < ‖φ.dir‖ + 1 := by positivity
  refine ⟨η / (‖φ.dir‖ + 1), div_pos hη hpos, fun τ hτ0 hτ1 x hx => ?_⟩
  by_cases hz : x + τ • φ.dir ∈ K
  swap
  · exact Or.inr hz
  left
  have hdist : dist x (x + τ • φ.dir) ≤ η := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hτ0.le]
    have h1 : τ < η / (‖φ.dir‖ + 1) := hτ1
    rw [lt_div_iff₀ hpos] at h1
    nlinarith [norm_nonneg φ.dir]
  have hxd : x ∈ φ.dom := hηd (Metric.mem_cthickening_of_dist_le x _ η K hz hdist)
  have hx2 : x ∈ closure Ω ∩ φ.dom := ⟨hx, hxd⟩
  rw [GraphChart.closure_inter_dom] at hx2
  obtain ⟨⟨x', t⟩, ⟨hx'B, ht0, hta⟩, rfl⟩ := hx2
  have hzd := hKd hz
  obtain ⟨⟨y', s⟩, ⟨hy'B, hsa1, hsa2⟩, hys⟩ := hzd
  have hshift : φ.map (x', t + τ) = φ.map (x', t) + τ • φ.dir := graphMap_add_right x' t τ
  have hinj : (y', s) = (x', t + τ) := by
    have h1 : φ.map (y', s) = φ.map (x', t + τ) := by rw [hys, hshift]
    have h2 : graphMap φ.i φ.γ φ.sgn (y', s) = graphMap φ.i φ.γ φ.sgn (x', t + τ) := h1
    have := congrArg (graphMapInv φ.i φ.γ φ.sgn) h2
    rwa [graphMapInv_graphMap φ.sgn_sq, graphMapInv_graphMap φ.sgn_sq] at this
  obtain ⟨h1, h2⟩ := Prod.mk.inj hinj
  have hmem : φ.map (x', t) + τ • φ.dir ∈ Ω ∩ φ.dom := by
    have hinter : Ω ∩ φ.dom = φ.map '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := φ.inter_eq
    rw [hinter]
    refine ⟨(y', s), ⟨hy'B, ?_, hsa2⟩, hys⟩
    simp only at h2 ⊢
    rw [h2]; linarith
  exact hmem.1

end PDE.TraceLane
