module

public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Finite greedy disjoint selection

This module extracts a pairwise disjoint subfamily from a finite indexed
family of nonempty sets. Every original set meets a selected set whose weight
is at least as large. No geometry or measure structure is required.
-/

@[expose] public section

namespace PDE

/-- A finite family of nonempty sets admits a pairwise disjoint subfamily such
that every original set meets a selected set of at least the same weight. -/
theorem exists_pairwiseDisjoint_finset_of_nonempty
    {ι α : Type*} (s : Finset ι) (B : ι → Set α) (r : ι → ℝ)
    (hne : ∀ a ∈ s, (B a).Nonempty) :
    ∃ t : Finset ι, t ⊆ s ∧ (t : Set ι).PairwiseDisjoint B ∧
      ∀ a ∈ s, ∃ b ∈ t, (B a ∩ B b).Nonempty ∧ r a ≤ r b := by
  classical
  revert hne
  refine Finset.strongInductionOn s ?_
  intro s ih hne
  by_cases hs : s = ∅
  · subst s
    refine ⟨∅, Finset.Subset.rfl, ?_, by simp⟩
    simp
  · obtain ⟨c, hc, hcmax⟩ :=
      Finset.exists_max_image s r (Finset.nonempty_iff_ne_empty.mpr hs)
    let u := s.filter fun b => Disjoint (B b) (B c)
    have hcu : c ∉ u := by
      intro h
      have hdis : Disjoint (B c) (B c) := (Finset.mem_filter.mp h).2
      obtain ⟨x, hx⟩ := hne c hc
      exact (Set.not_disjoint_iff_nonempty_inter.mpr ⟨x, hx, hx⟩) hdis
    have hus : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset _ _, fun h => hcu (h ▸ hc)⟩
    obtain ⟨t, htu, ht_disjoint, ht_cover⟩ := ih u hus fun a ha =>
      hne a (Finset.filter_subset _ _ ha)
    refine ⟨insert c t, ?_, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert] at ha
      exact ha.elim (fun h => h ▸ hc) (fun h => Finset.filter_subset _ _ (htu h))
    · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
      refine ⟨ht_disjoint, fun b hb _ => ?_⟩
      exact (Finset.mem_filter.mp (htu hb)).2.symm
    · intro a ha
      by_cases hau : a ∈ u
      · obtain ⟨b, hbt, hab, hr⟩ := ht_cover a hau
        exact ⟨b, Finset.mem_insert_of_mem hbt, hab, hr⟩
      · have hnot : ¬Disjoint (B a) (B c) := by
          intro hdis
          exact hau (Finset.mem_filter.mpr ⟨ha, hdis⟩)
        exact ⟨c, Finset.mem_insert_self c t, Set.not_disjoint_iff_nonempty_inter.mp hnot,
          hcmax a ha⟩

end PDE
