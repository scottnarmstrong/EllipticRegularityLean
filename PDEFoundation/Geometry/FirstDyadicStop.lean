module

public import PDEFoundation.Geometry.DyadicBoxDisjoint

/-! # Literal first stopping paths in a dyadic tree -/

@[expose] public section

namespace PDE

open BoxIntegral

/-- A first stopping path satisfies the predicate, while none of its proper
prefixes does. This definition makes the stopping selection literal. -/
def IsFirstPrefixStop {α : Type*} (bad : List α → Prop) (p : List α) : Prop :=
  bad p ∧ ∀ q, q <+: p → q ≠ p → ¬ bad q

/-- Every path satisfying the stopping predicate has a first stopping prefix. -/
theorem exists_firstPrefixStop {α : Type*} (bad : List α → Prop)
    {p : List α} (hp : bad p) :
    ∃ q, q <+: p ∧ IsFirstPrefixStop bad q := by
  classical
  have hex : ∃ n : ℕ, ∃ q : List α, q <+: p ∧ q.length = n ∧ bad q :=
    ⟨p.length, p, List.prefix_refl _, rfl, hp⟩
  obtain ⟨q, hqp, hlen, hbad⟩ := Nat.find_spec hex
  refine ⟨q, hqp, hbad, ?_⟩
  intro r hrq hrne hrbad
  have hmin : Nat.find hex ≤ r.length :=
    Nat.find_le ⟨r, hrq.trans hqp, rfl, hrbad⟩
  have heq : r = q := hrq.eq_of_length_le (by omega)
  exact hrne heq

/-- Distinct first stopping paths are incomparable in the prefix order. -/
theorem firstPrefixStop_incomparable {α : Type*} {bad : List α → Prop}
    {p q : List α} (hp : IsFirstPrefixStop bad p)
    (hq : IsFirstPrefixStop bad q) (hne : p ≠ q) :
    ¬ p <+: q ∧ ¬ q <+: p := by
  constructor
  · intro hpq
    exact hq.2 p hpq hne hp.1
  · intro hqp
    exact hp.2 q hqp hne.symm hq.1

/-- When the root does not satisfy the predicate, every first stop is a strict
descendant. -/
theorem firstPrefixStop_ne_nil {α : Type*} {bad : List α → Prop}
    (hroot : ¬ bad []) {p : List α} (hp : IsFirstPrefixStop bad p) : p ≠ [] := by
  intro heq
  exact hroot (heq ▸ hp.1)

/-- Distinct literal first stopping descendants have disjoint half-open
carriers. No disjointness is assumed by the selection. -/
theorem disjoint_dyadicDescendant_of_firstPrefixStop {d : ℕ}
    (I : Box (Fin d)) {bad : List (Set (Fin d)) → Prop}
    {p q : List (Set (Fin d))} (hp : IsFirstPrefixStop bad p)
    (hq : IsFirstPrefixStop bad q) (hne : p ≠ q) :
    Disjoint (dyadicDescendant I p : Set (Vec d))
      (dyadicDescendant I q : Set (Vec d)) := by
  obtain ⟨hpq, hqp⟩ := firstPrefixStop_incomparable hp hq hne
  exact disjoint_dyadicDescendant_of_incomparable I hpq hqp

end PDE
