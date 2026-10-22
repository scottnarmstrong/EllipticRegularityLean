module

public import PDEFoundation.Geometry.DyadicBoxDisjoint

/-!
# Fixed-depth partition by literal dyadic descendants

At every depth, the literal descendants obtained by repeated center splitting
partition the half-open carrier of the root box.
-/

@[expose] public section

namespace PDE

open BoxIntegral

/-- Every point of a box belongs to exactly one literal dyadic descendant at
each prescribed depth. -/
theorem existsUnique_mem_dyadicDescendant_of_length {d : ℕ}
    (I : Box (Fin d)) {x : Vec d} (hx : x ∈ (I : Set (Vec d))) (n : ℕ) :
    ∃! p : List (Set (Fin d)),
      p.length = n ∧ x ∈ (dyadicDescendant I p : Set (Vec d)) := by
  have hexists : ∃ p : List (Set (Fin d)),
      p.length = n ∧ x ∈ (dyadicDescendant I p : Set (Vec d)) := by
    induction n generalizing I with
    | zero => exact ⟨[], rfl, hx⟩
    | succ n ih =>
        obtain ⟨s, hxs⟩ := Box.exists_mem_splitCenterBox.mpr hx
        obtain ⟨p, hplen, hxp⟩ := ih (I := I.splitCenterBox s) hxs
        exact ⟨s :: p, by simp only [List.length_cons, hplen], hxp⟩
  obtain ⟨p, hp⟩ := hexists
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hqp
  have hdisjoint := disjoint_dyadicDescendant_of_length_eq I
    (hp.1.trans hq.1.symm) (fun hpq => hqp hpq.symm)
  exact (Set.disjoint_left.mp hdisjoint hp.2) hq.2

end PDE
