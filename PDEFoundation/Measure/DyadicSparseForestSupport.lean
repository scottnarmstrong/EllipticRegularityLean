module

public import PDEFoundation.Measure.DyadicSparseSum

/-! # Support and root-box geometry for dyadic sparse forests -/

@[expose] public section

namespace PDE

open BoxIntegral Set

noncomputable section

variable {d : ℕ}

/-- The literal countable sparse sum vanishes outside its root box. -/
theorem dyadicSparseSum_eq_zero_of_not_mem
    (I : Box (Fin d)) (S : Set (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ) {x : Vec d}
    (hx : x ∉ (I : Set (Vec d))) :
    dyadicSparseSum I S a x = 0 := by
  unfold dyadicSparseSum
  rw [ENNReal.tsum_eq_zero]
  intro q
  by_cases hq : q ∈ S
  · rw [Set.indicator_of_mem hq]
    have hxq : x ∉ (dyadicDescendant I q : Set (Vec d)) := fun hxq =>
      hx (dyadicDescendant_le I q hxq)
    simp [Set.indicator, hxq]
  · rw [Set.indicator_of_notMem hq]

/-- Disjoint open interiors of two boxes force their literal half-open
carriers to be disjoint. -/
theorem disjoint_coe_of_disjoint_Ioo (I J : Box (Fin d))
    (hIJ : Disjoint (Box.Ioo I) (Box.Ioo J)) :
    Disjoint (I : Set (Vec d)) (J : Set (Vec d)) := by
  apply Set.disjoint_left.mpr
  intro x hxI hxJ
  let y : Vec d := fun i =>
    (max (I.lower i) (J.lower i) + min (I.upper i) (J.upper i)) / 2
  have hyI : y ∈ Box.Ioo I := by
    intro i _hi
    have hxIi := hxI i
    have hxJi := hxJ i
    dsimp only [y]
    constructor
    · have hlo : max (I.lower i) (J.lower i) < x i :=
        max_lt hxIi.1 hxJi.1
      have hup : x i ≤ min (I.upper i) (J.upper i) :=
        le_min hxIi.2 hxJi.2
      have hIlow : I.lower i ≤ max (I.lower i) (J.lower i) := le_max_left _ _
      linarith
    · have hlo : max (I.lower i) (J.lower i) < x i :=
        max_lt hxIi.1 hxJi.1
      have hup : x i ≤ min (I.upper i) (J.upper i) :=
        le_min hxIi.2 hxJi.2
      have hIup : min (I.upper i) (J.upper i) ≤ I.upper i := min_le_left _ _
      linarith
  have hyJ : y ∈ Box.Ioo J := by
    intro i _hi
    have hxIi := hxI i
    have hxJi := hxJ i
    dsimp only [y]
    constructor
    · have hlo : max (I.lower i) (J.lower i) < x i :=
        max_lt hxIi.1 hxJi.1
      have hup : x i ≤ min (I.upper i) (J.upper i) :=
        le_min hxIi.2 hxJi.2
      have hJlow : J.lower i ≤ max (I.lower i) (J.lower i) := le_max_right _ _
      linarith
    · have hlo : max (I.lower i) (J.lower i) < x i :=
        max_lt hxIi.1 hxJi.1
      have hup : x i ≤ min (I.upper i) (J.upper i) :=
        le_min hxIi.2 hxJi.2
      have hJup : min (I.upper i) (J.upper i) ≤ J.upper i := min_le_right _ _
      linarith
  exact Set.disjoint_left.mp hIJ hyI hyJ

end

end PDE
