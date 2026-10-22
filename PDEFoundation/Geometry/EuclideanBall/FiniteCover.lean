module

public import PDEFoundation.Analysis.FiniteGreedyCover
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Finite disjoint selection of round balls with triple-dilate coverage -/

@[expose] public section

namespace PDE

/-- An intersecting ball of no greater radius lies in the triple dilate. -/
theorem euclideanBall_subset_triple_of_inter_nonempty
    {d : ℕ} {z c : Vec d} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R)
    (hinter : (euclideanBall z r ∩ euclideanBall c R).Nonempty) :
    euclideanBall z r ⊆ euclideanBall c (3 * R) := by
  obtain ⟨y, hyz, hyc⟩ := hinter
  have hyzNorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hyz
  have hycNorm := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hyc
  have hcenter : vecEuclideanNorm (z - c) ≤
      vecEuclideanNorm (y - z) + vecEuclideanNorm (y - c) := by
    rw [vecEuclideanNorm_sub_comm y z]
    have hsum : z - c = (z - y) + (y - c) := by abel
    rw [hsum]
    exact vecEuclideanNorm_add_le _ _
  apply euclideanBall_subset_of_center_norm_add_le hr (by positivity)
  linarith only [hcenter, hyzNorm, hycNorm, hrR]

/-- A finite family of positive-radius round balls has a disjoint subfamily
whose triple dilates cover every original ball. -/
theorem exists_pairwiseDisjoint_euclideanBalls_covering_triples
    {d : ℕ} {ι : Type*} (s : Finset ι) (z : ι → Vec d) (r : ι → ℝ)
    (hr : ∀ a ∈ s, 0 < r a) :
    ∃ t : Finset ι, t ⊆ s ∧
      (t : Set ι).PairwiseDisjoint (fun a => euclideanBall (z a) (r a)) ∧
      ∀ a ∈ s, ∃ b ∈ t,
        euclideanBall (z a) (r a) ⊆ euclideanBall (z b) (3 * r b) := by
  obtain ⟨t, hts, hdisjoint, hcover⟩ := exists_pairwiseDisjoint_finset_of_nonempty s
    (fun a => euclideanBall (z a) (r a)) r
    (fun a ha => ⟨z a, center_mem_euclideanBall (z a) (hr a ha)⟩)
  refine ⟨t, hts, hdisjoint, ?_⟩
  intro a ha
  obtain ⟨b, hb, hinter, hsize⟩ := hcover a ha
  exact ⟨b, hb, euclideanBall_subset_triple_of_inter_nonempty
    (hr a ha) (hr b (hts hb)) hsize hinter⟩

end PDE
