module

public import PDEFoundation.Sobolev.Trace.Chart.AtlasChart
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Trace atlas of a bounded `C¹` domain

The frontier of a bounded open set is compact; it is covered by finitely many graph-chart
cylinders, and a smooth partition of unity subordinate to the (bounded) cylinders, taken on a closed
thickening of the frontier, gives the atlas data.
-/

@[expose] public section

namespace PDE.TraceLane

open Set Filter Topology Metric
open scoped Manifold

/-- A bounded open set with `C¹` boundary has a trace atlas. -/
theorem exists_traceAtlas {n : ℕ} {Ω : Set (Vec (n + 1))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩ : HasC1Boundary Ω) : Nonempty (TraceAtlas Ω) := by
  classical
  have hK : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩb.closure.subset frontier_subset_closure)
  choose ch hch using fun x : frontier Ω => exists_graphChart hΩo hΩ x.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : frontier Ω => (ch x).dom)
    (fun x => (ch x).atlas_isOpen_dom) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hch ⟨x, hx⟩⟩)
  obtain ⟨M, hM⟩ := hK.isBounded.subset_ball (0 : Vec (n + 1))
  set O : Set (Vec (n + 1)) := (⋃ x ∈ t, (ch x).dom) ∩ ball 0 M with hO
  have hOo : IsOpen O :=
    (isOpen_biUnion fun x _ => (ch x).atlas_isOpen_dom).inter isOpen_ball
  have hKO : frontier Ω ⊆ O := fun x hx => ⟨ht hx, hM hx⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hOo hKO
  let U : t → Set (Vec (n + 1)) := fun j => (ch j.1).dom ∩ ball 0 M
  have hUo : ∀ j, IsOpen (U j) := fun j => (ch j.1).atlas_isOpen_dom.inter isOpen_ball
  have hcov : cthickening δ (frontier Ω) ⊆ ⋃ j, U j := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hδO hy
    obtain ⟨x, hxt, hd⟩ := mem_iUnion₂.1 hy1
    exact mem_iUnion.2 ⟨⟨x, hxt⟩, hd, hy2⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Vec (n + 1)))
    isClosed_cthickening U hUo hcov
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨{ N := Fintype.card t, chart := fun j => ch (e.symm j).1, ζ := fun j => f (e.symm j),
            ζ_smooth := fun j => contMDiff_iff_contDiff.1 ((f (e.symm j)).contMDiff),
            ζ_nonneg := fun j x => f.nonneg _ x,
            ζ_compact := ?_, ζ_tsupport := fun j => (hf (e.symm j)).trans inter_subset_left,
            V := thickening δ (frontier Ω), V_open := isOpen_thickening,
            frontier_subset := self_subset_thickening hδ _, sum_eq_one := ?_ }⟩
  · intro j
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec (n + 1)) M)
      (isClosed_tsupport _) ?_
    exact ((hf (e.symm j)).trans inter_subset_right).trans ball_subset_closedBall
  · intro x hx
    have hxs : x ∈ cthickening δ (frontier Ω) := thickening_subset_cthickening _ _ hx
    have h1 := f.sum_eq_one hxs
    rw [finsum_eq_sum_of_fintype] at h1
    rw [← h1]
    exact Equiv.sum_comp e.symm (fun i => f i x)

end PDE.TraceLane
