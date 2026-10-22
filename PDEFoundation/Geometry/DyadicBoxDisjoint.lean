module

public import PDEFoundation.Geometry.DyadicBox

/-!
# Nesting and disjointness of literal dyadic descendants

Literal paths through repeated center splits are nested along prefixes. Paths
that are incomparable in the prefix order give disjoint half-open boxes.
-/

@[expose] public section

namespace PDE

open BoxIntegral

/-- Extending a literal dyadic path produces a descendant contained in the
box at the original path. -/
theorem dyadicDescendant_subset_of_isPrefix {d : ℕ}
    (I : Box (Fin d)) {p q : List (Set (Fin d))} (hpq : p <+: q) :
    (dyadicDescendant I q : Set (Vec d)) ⊆ dyadicDescendant I p := by
  obtain ⟨r, rfl⟩ := hpq
  rw [dyadicDescendant_append]
  exact dyadicDescendant_le (dyadicDescendant I p) r

/-- Descendants along two prefix-incomparable literal paths are disjoint as
half-open sets. -/
theorem disjoint_dyadicDescendant_of_incomparable {d : ℕ}
    (I : Box (Fin d)) {p q : List (Set (Fin d))}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    Disjoint (dyadicDescendant I p : Set (Vec d))
      (dyadicDescendant I q : Set (Vec d)) := by
  induction p generalizing I q with
  | nil => exact (hpq List.nil_prefix).elim
  | cons s ss ih =>
      cases q with
      | nil => exact (hqp List.nil_prefix).elim
      | cons t tt =>
          by_cases hst : s = t
          · subst t
            exact ih (I.splitCenterBox s)
              (fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩))
              (fun h => hqp (List.cons_prefix_cons.2 ⟨rfl, h⟩))
          · exact Disjoint.mono
              (dyadicDescendant_le (I.splitCenterBox s) ss)
              (dyadicDescendant_le (I.splitCenterBox t) tt)
              (I.disjoint_splitCenterBox hst)

/-- Distinct literal paths of the same depth give disjoint half-open dyadic
descendants. -/
theorem disjoint_dyadicDescendant_of_length_eq {d : ℕ}
    (I : Box (Fin d)) {p q : List (Set (Fin d))}
    (hlen : p.length = q.length) (hpq : p ≠ q) :
    Disjoint (dyadicDescendant I p : Set (Vec d))
      (dyadicDescendant I q : Set (Vec d)) := by
  apply disjoint_dyadicDescendant_of_incomparable I
  · intro hpref
    exact hpq (List.IsPrefix.eq_of_length hpref hlen)
  · intro hpref
    exact hpq (List.IsPrefix.eq_of_length hpref hlen.symm).symm

end PDE
