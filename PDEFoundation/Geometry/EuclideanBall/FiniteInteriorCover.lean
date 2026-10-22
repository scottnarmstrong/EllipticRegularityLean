module

public import PDEFoundation.Geometry.EuclideanBall.Topology

/-! # Finite interior covers of a Euclidean ball -/

@[expose] public section

namespace PDE

open Set

/-- The closed half ball has a finite cover by smaller round balls whose
concentric radius-`r` enlargements remain inside the unit ball. -/
theorem exists_finset_euclideanBall_cover_closedHalf
    {d : ℕ} {r : ℝ} (hr : 0 < r) (hrQuarter : r ≤ 1 / 4) :
    ∃ s : Finset (Vec d),
      (∀ z ∈ s, z ∈ euclideanClosedBall (0 : Vec d) (1 / 2)) ∧
      euclideanClosedBall (0 : Vec d) (1 / 2) ⊆
        ⋃ z ∈ s, euclideanBall z (r / 2) ∧
      (∀ z ∈ s, euclideanBall z r ⊆ euclideanBall (0 : Vec d) 1) := by
  classical
  let K := euclideanClosedBall (0 : Vec d) (1 / 2)
  let inner : K → Set (Vec d) := fun z => euclideanBall z.1 (r / 2)
  have hcover : K ⊆ ⋃ z : K, inner z := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact center_mem_euclideanBall x (by linarith)
  obtain ⟨t, ht⟩ :=
    (isCompact_euclideanClosedBall (0 : Vec d)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)).elim_finite_subcover
      inner (fun z => isOpen_euclideanBall _ _) hcover
  let s : Finset (Vec d) := t.image Subtype.val
  refine ⟨s, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact y.2
  · intro x hx
    have hx' : x ∈ ⋃ z ∈ t, inner z := ht hx
    simp only [Set.mem_iUnion] at hx' ⊢
    obtain ⟨z, hz, hxz⟩ := hx'
    exact ⟨z.1, Finset.mem_image.2 ⟨z, hz, rfl⟩, hxz⟩
  · intro z hz x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    have hxy := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
    have hy0 : vecEuclideanNorm (y.1 - 0) ≤ 1 / 2 :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 y.2
    have htri : vecEuclideanNorm (x - 0) ≤
        vecEuclideanNorm (x - y.1) + vecEuclideanNorm (y.1 - 0) := by
      calc
        vecEuclideanNorm (x - 0) =
            vecEuclideanNorm ((x - y.1) + (y.1 - 0)) := by
          congr 1
          ext i
          simp
        _ ≤ _ := vecEuclideanNorm_add_le _ _
    linarith

end PDE
