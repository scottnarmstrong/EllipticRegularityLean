module

public import PDEFoundation.Geometry.DyadicBox

/-!
# Volume of literal dyadic descendants

This file records the exact Lebesgue-volume scaling under center splitting of
Mathlib boxes. Volumes are stated in real form, matching the finite-volume
normalizations used by averages.
-/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory

/-- Every center-split child has `2 ^ d` times less volume than its parent. -/
theorem volume_splitCenterBox_toReal {d : ℕ}
    (I : Box (Fin d)) (s : Set (Fin d)) :
    (volume (I.splitCenterBox s : Set (Vec d))).toReal =
      (volume (I : Set (Vec d))).toReal / (2 : ℝ) ^ d := by
  rw [Box.volume_apply', Box.volume_apply']
  simp_rw [I.upper_sub_lower_splitCenterBox s]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Equivalently, a parent has exactly `2 ^ d` times the volume of each
center-split child. -/
theorem volume_toReal_eq_pow_mul_volume_splitCenterBox_toReal {d : ℕ}
    (I : Box (Fin d)) (s : Set (Fin d)) :
    (volume (I : Set (Vec d))).toReal =
      (2 : ℝ) ^ d *
        (volume (I.splitCenterBox s : Set (Vec d))).toReal := by
  rw [volume_splitCenterBox_toReal]
  field_simp

/-- A descendant at path length `k` has `2 ^ (d * k)` times less volume than
its root. -/
theorem volume_dyadicDescendant_toReal {d : ℕ}
    (I : Box (Fin d)) (p : List (Set (Fin d))) :
    (volume (dyadicDescendant I p : Set (Vec d))).toReal =
      (volume (I : Set (Vec d))).toReal /
        (2 : ℝ) ^ (d * p.length) := by
  rw [Box.volume_apply', Box.volume_apply']
  simp_rw [upper_sub_lower_dyadicDescendant]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm]

end PDE
