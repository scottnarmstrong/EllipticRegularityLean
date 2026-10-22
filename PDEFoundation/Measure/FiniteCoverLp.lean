module

public import PDEFoundation.Measure.LpSpace

/-! # Gluing local `Lᵖ` bounds over finite covers -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Local `Lᵖ` membership over a finite measurable cover glues to the target,
with its norm bounded by the sum of the local norms. -/
theorem memLp_and_eLpNorm_le_sum_of_finset_cover
    {d : ℕ} {E ι : Type*} [NormedAddCommGroup E] [DecidableEq ι]
    {p : ENNReal} (hp : 1 ≤ p) (f : Vec d → E)
    (U : ι → Set (Vec d)) (s : Finset ι) (V : Set (Vec d))
    (hU : ∀ i ∈ s, MeasurableSet (U i)) (hV : MeasurableSet V)
    (hcover : V ⊆ ⋃ i ∈ s, U i)
    (hlocal : ∀ i ∈ s, MemLp f p (volumeOn (U i))) :
    MemLp f p (volumeOn V) ∧
      eLpNorm f p (volumeOn V) ≤
        ∑ i ∈ s, eLpNorm f p (volumeOn (U i)) := by
  classical
  have aux : ∀ (t : Finset ι) (W : Set (Vec d)),
      (∀ i ∈ t, MeasurableSet (U i)) → MeasurableSet W →
      W ⊆ ⋃ i ∈ t, U i →
      (∀ i ∈ t, MemLp f p (volumeOn (U i))) →
      MemLp f p (volumeOn W) ∧
        eLpNorm f p (volumeOn W) ≤
          ∑ i ∈ t, eLpNorm f p (volumeOn (U i)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro W _ hW hcov _
        have hWempty : W = ∅ := Set.subset_empty_iff.mp (by simpa using hcov)
        subst W
        simp [volumeOn]
    | @insert a t ha ih =>
        intro W hUt hW hcov hmem
        let A := W ∩ U a
        let B := W \ U a
        have hUa : MeasurableSet (U a) := hUt a (Finset.mem_insert_self a t)
        have hAmeas : MeasurableSet A := hW.inter hUa
        have hBmeas : MeasurableSet B := hW.diff hUa
        have hAsub : volumeOn A ≤ volumeOn (U a) :=
          Measure.restrict_mono inter_subset_right le_rfl
        have hAmem : MemLp f p (volumeOn A) :=
          (hmem a (Finset.mem_insert_self a t)).mono_measure hAsub
        have hBcover : B ⊆ ⋃ i ∈ t, U i := by
          intro x hx
          have hxcover := hcov hx.1
          simp only [Finset.set_biUnion_insert] at hxcover
          exact hxcover.resolve_left hx.2
        have hBt := ih B
          (fun i hi => hUt i (Finset.mem_insert_of_mem hi)) hBmeas hBcover
          (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
        have hUnion : A ∪ B = W := by
          ext x
          simp only [A, B, mem_union, mem_inter_iff, mem_sdiff]
          tauto
        have hDisjoint : Disjoint A B := by
          apply Set.disjoint_left.2
          intro x hxA hxB
          exact hxB.2 hxA.2
        have hAind : MemLp (A.indicator f) p volume :=
          (memLp_indicator_iff_restrict hAmeas).2 hAmem
        have hBind : MemLp (B.indicator f) p volume :=
          (memLp_indicator_iff_restrict hBmeas).2 hBt.1
        have hWind : MemLp (W.indicator f) p volume := by
          rw [← hUnion, indicator_union_of_disjoint hDisjoint]
          exact hAind.add hBind
        have hindEq : W.indicator f = A.indicator f + B.indicator f := by
          rw [← hUnion]
          simpa only [Pi.add_apply] using! indicator_union_of_disjoint hDisjoint f
        refine ⟨(memLp_indicator_iff_restrict hW).1 hWind, ?_⟩
        calc
          eLpNorm f p (volumeOn W) = eLpNorm (W.indicator f) p volume :=
            (eLpNorm_indicator_eq_eLpNorm_restrict hW).symm
          _ = eLpNorm (A.indicator f + B.indicator f) p volume := by
            rw [hindEq]
          _ ≤ eLpNorm (A.indicator f) p volume +
              eLpNorm (B.indicator f) p volume :=
            eLpNorm_add_le
              hp
          _ = eLpNorm f p (volumeOn A) + eLpNorm f p (volumeOn B) := by
            rw [eLpNorm_indicator_eq_eLpNorm_restrict hAmeas,
              eLpNorm_indicator_eq_eLpNorm_restrict hBmeas]
          _ ≤ eLpNorm f p (volumeOn (U a)) +
              ∑ i ∈ t, eLpNorm f p (volumeOn (U i)) :=
            add_le_add (eLpNorm_mono_measure f hAsub) hBt.2
          _ = ∑ i ∈ insert a t, eLpNorm f p (volumeOn (U i)) := by
            rw [Finset.sum_insert ha]
  exact aux s V hU hV hcover hlocal

end PDE
