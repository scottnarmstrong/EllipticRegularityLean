module

public import PDEFoundation.Sobolev.Trace.Chart.Facts

/-!
# Topology of a graph chart cylinder

The chart cylinder `φ.dom` is open, and inside it the frontier (closure) of `Ω` is the image of
`B_r(c) × {0}` (`B_r(c) × [0, a)`).
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

/-- The chart map as a homeomorphism. -/
def graphHomeo {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) (sgn : ℝ) (hs : sgn ^ 2 = 1)
    (hγ : ContDiff ℝ 1 γ) : Vec n × ℝ ≃ₜ Vec (n + 1) where
  toFun := graphMap i γ sgn
  invFun := graphMapInv i γ sgn
  left_inv := graphMapInv_graphMap hs
  right_inv := graphMap_graphMapInv hs
  continuous_toFun := (contDiff_graphMap hγ).continuous
  continuous_invFun := (contDiff_graphMapInv hγ).continuous

namespace GraphChart

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The chart map of a chart, as a homeomorphism. -/
def homeo (φ : GraphChart Ω) : Vec n × ℝ ≃ₜ Vec (n + 1) :=
  graphHomeo φ.i φ.γ φ.sgn φ.sgn_sq φ.γ_contDiff

theorem homeo_apply (φ : GraphChart Ω) (z : Vec n × ℝ) : φ.homeo z = φ.map z := rfl

theorem isOpen_dom (φ : GraphChart Ω) : IsOpen φ.dom := by
  have : φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) := rfl
  rw [this]
  exact φ.homeo.isOpenMap _
    ((isOpen_euclideanBall _ _).prod isOpen_Ioo)

private theorem closure_ball_prod (φ : GraphChart Ω) :
    closure (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) ∩ (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) =
      euclideanBall φ.c φ.r ×ˢ Ico 0 φ.a := by
  have hB := isOpen_euclideanBall φ.c φ.r
  have ha := φ.a_pos
  rw [closure_prod_eq, closure_Ioo ha.ne]
  ext ⟨x, t⟩
  simp only [mem_inter_iff, mem_prod, mem_Icc, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨⟨_, h0, h1⟩, h2, h3, h4⟩
    exact ⟨h2, h0, h4⟩
  · rintro ⟨h2, h0, h4⟩
    exact ⟨⟨subset_closure h2, h0, h4.le⟩, h2, by linarith, h4⟩

private theorem closure_dom_eq (φ : GraphChart Ω) :
    closure Ω ∩ φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ico 0 φ.a) := by
  have hU := φ.isOpen_dom
  have h1 : closure Ω ∩ φ.dom = closure (Ω ∩ φ.dom) ∩ φ.dom := by
    refine Subset.antisymm (fun x hx => ⟨?_, hx.2⟩) (inter_subset_inter_left _
      (closure_mono inter_subset_left))
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨y, hyV, hyΩ⟩ := mem_closure_iff.1 hx.1 (V ∩ φ.dom) (hV.inter hU) ⟨hxV, hx.2⟩
    exact ⟨y, hyV.1, hyΩ, hyV.2⟩
  have h2 : Ω ∩ φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := φ.inter_eq
  rw [h1, h2]
  have h3 := φ.homeo.image_closure (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a)
  have h4 : φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) := rfl
  rw [← h3, h4, ← Set.image_inter φ.homeo.injective, closure_ball_prod]

theorem closure_inter_dom (φ : GraphChart Ω) :
    closure Ω ∩ φ.dom = φ.map '' (euclideanBall φ.c φ.r ×ˢ Ico 0 φ.a) :=
  closure_dom_eq φ

theorem frontier_inter_dom (φ : GraphChart Ω) :
    frontier Ω ∩ φ.dom = φ.map '' (euclideanBall φ.c φ.r ×ˢ {0}) := by
  have hU := φ.isOpen_dom
  have h2 : Ω ∩ φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := φ.inter_eq
  have hint : interior Ω ∩ φ.dom = φ.homeo '' (euclideanBall φ.c φ.r ×ˢ Ioo 0 φ.a) := by
    rw [← h2, ← interior_eq_iff_isOpen.mpr hU, ← interior_inter,
      interior_eq_iff_isOpen.mpr hU, h2, ← φ.homeo.image_interior,
      interior_eq_iff_isOpen.mpr ((isOpen_euclideanBall _ _).prod isOpen_Ioo)]
  have : frontier Ω ∩ φ.dom = (closure Ω ∩ φ.dom) \ (interior Ω ∩ φ.dom) := by
    ext x; simp only [frontier, mem_inter_iff, mem_sdiff]; tauto
  rw [this, closure_dom_eq, hint, ← Set.image_sdiff φ.homeo.injective]
  change _ = φ.homeo '' _
  congr 1
  ext ⟨x, t⟩
  simp only [mem_sdiff, mem_prod, mem_Ico, mem_Ioo, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hx, h0, _⟩, hn⟩
    refine ⟨hx, ?_⟩
    by_contra ht
    exact hn ⟨hx, lt_of_le_of_ne h0 (Ne.symm ht), ‹_›⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨hx, le_rfl, φ.a_pos⟩, fun h => lt_irrefl _ h.2.1⟩

end GraphChart

end PDE.TraceLane
