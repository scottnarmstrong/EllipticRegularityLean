module

public import PDEFoundation.Measure.DyadicSparseRemainder
public import PDEFoundation.Measure.DyadicStoppingFiniteChains

/-! # Global disjointness of recursive dyadic sparse remainders -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set

/-- A remainder belonging to generation `n` lies in the part of the current
stopping region removed before generation `n + 1`. -/
theorem dyadicSparseRemainder_subset_region_diff
    {d m : ℕ} (I : Box (Fin d)) (g : Vec d → Vec m) (n : ℕ)
    {p : List (Set (Fin d))} (hp : p ∈ dyadicStoppingGeneration I g n) :
    dyadicSparseRemainder I g p ⊆
      dyadicStoppingRegion I g n \ dyadicStoppingRegion I g (n + 1) := by
  intro x hx
  refine ⟨Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx.1⟩, ?_⟩
  intro hnext
  obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp hnext
  have hzmem := z.2
  rw [mem_dyadicStoppingGeneration_succ] at hzmem
  obtain ⟨r, hr, q, hq, heq⟩ := hzmem
  by_cases hparent : r = p
  · subst r
    apply hx.2
    unfold dyadicOscillationStopUnion
    refine Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, ?_⟩⟩
    rw [heq, dyadicDescendant_append] at hxz
    exact hxz
  · have hparents := pairwiseDisjoint_dyadicStoppingGeneration I g n hp hr
      (Ne.symm hparent)
    have hsub : (dyadicDescendant I z.1 : Set (Vec d)) ⊆
        (dyadicDescendant I r : Set (Vec d)) := by
      rw [heq, dyadicDescendant_append]
      exact dyadicDescendant_le (dyadicDescendant I r) q
    exact (Set.disjoint_left.mp hparents hx.1) (hsub hxz)

/-- The actual remainders indexed by every path in the recursively generated
sparse family are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicSparseRemainder {d m : ℕ}
    (I : Box (Fin d)) (g : Vec d → Vec m) :
    (dyadicSparseFamily I g).Pairwise
      (fun p q => Disjoint (dyadicSparseRemainder I g p)
        (dyadicSparseRemainder I g q)) := by
  intro p hp q hq hpq
  obtain ⟨n, hn⟩ := hp
  obtain ⟨k, hk⟩ := hq
  rcases lt_trichotomy n k with hnk | heq | hkn
  · apply Set.disjoint_left.mpr
    intro x hxp hxq
    have hpout := (dyadicSparseRemainder_subset_region_diff I g n hn hxp).2
    have hqin := (dyadicSparseRemainder_subset_region_diff I g k hk hxq).1
    exact hpout (antitone_dyadicStoppingRegion I g (Nat.succ_le_iff.mpr hnk) hqin)
  · subst k
    exact (pairwiseDisjoint_dyadicStoppingGeneration I g n hn hk hpq).mono
      (dyadicSparseRemainder_subset I g p) (dyadicSparseRemainder_subset I g q)
  · apply Set.disjoint_left.mpr
    intro x hxp hxq
    have hqout := (dyadicSparseRemainder_subset_region_diff I g k hk hxq).2
    have hpin := (dyadicSparseRemainder_subset_region_diff I g n hn hxp).1
    exact hqout (antitone_dyadicStoppingRegion I g (Nat.succ_le_iff.mpr hkn) hpin)

end PDE
