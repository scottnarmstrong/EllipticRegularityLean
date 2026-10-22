module

public import PDEFoundation.Geometry.DyadicBoxVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The supremum-coordinate width of a nonzero-dimensional box is positive. -/
theorem norm_upper_sub_lower_pos (I : Box (Fin d)) (hd : 0 < d) :
    0 < ‖I.upper - I.lower‖ := by
  let i : Fin d := ⟨0, hd⟩
  have hi : 0 < (I.upper - I.lower) i := by
    simpa only [Pi.sub_apply] using sub_pos.mpr (I.lower_lt_upper i)
  have hle : |(I.upper - I.lower) i| ≤ ‖I.upper - I.lower‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg (I.upper - I.lower))).mp le_rfl i
  exact (abs_pos.mpr hi.ne').trans_le hle

/-- The natural containing-cube radius of a dyadic descendant is positive in
nonzero dimension. -/
theorem dyadicDescendant_supRadius_pos (I : Box (Fin d))
    (p : List (Set (Fin d))) (hd : 0 < d) :
    0 < ‖I.upper - I.lower‖ / (2 : ℝ) ^ p.length :=
  div_pos (norm_upper_sub_lower_pos I hd) (pow_pos (by norm_num) _)

/-- The real volume of a box is positive. -/
theorem volume_box_toReal_pos (I : Box (Fin d)) :
    0 < (volume (I : Set (Vec d))).toReal := by
  rw [Box.volume_apply']
  exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)

/-- Exact ratio between the native closed sup-cube at the descendant scale
and the dyadic descendant. -/
theorem volume_closedBall_dyadicDescendant_ratio
    (I : Box (Fin d)) (p : List (Set (Fin d))) (x : Vec d)
    (_hx : x ∈ (dyadicDescendant I p : Set (Vec d))) (hd : 0 < d) :
    let R := ‖I.upper - I.lower‖
    let r := R / (2 : ℝ) ^ p.length
    (volume (Metric.closedBall x r)).toReal =
      ((2 * R) ^ d / (volume (I : Set (Vec d))).toReal) *
        (volume (dyadicDescendant I p : Set (Vec d))).toReal := by
  dsimp only
  have hR : 0 < ‖I.upper - I.lower‖ := norm_upper_sub_lower_pos I hd
  have hr : 0 < ‖I.upper - I.lower‖ / (2 : ℝ) ^ p.length :=
    dyadicDescendant_supRadius_pos I p hd
  have hV : 0 < (volume (I : Set (Vec d))).toReal := volume_box_toReal_pos I
  rw [Real.volume_pi_closedBall x hr.le, ENNReal.toReal_ofReal]
  · rw [Fintype.card_fin, volume_dyadicDescendant_toReal]
    rw [show 2 * (‖I.upper - I.lower‖ / (2 : ℝ) ^ p.length) =
      (2 * ‖I.upper - I.lower‖) / (2 : ℝ) ^ p.length by ring]
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  · positivity

/-- The volume-ratio constant is nonnegative. -/
theorem dyadicDescendant_volumeRatioConstant_nonneg
    (I : Box (Fin d)) :
    0 ≤ (2 * ‖I.upper - I.lower‖) ^ d /
      (volume (I : Set (Vec d))).toReal := by
  positivity

/-- Inequality form of the exact closed-cube/descendant volume ratio. -/
theorem volume_closedBall_dyadicDescendant_le
    (I : Box (Fin d)) (p : List (Set (Fin d))) (x : Vec d)
    (hx : x ∈ (dyadicDescendant I p : Set (Vec d))) (hd : 0 < d) :
    let R := ‖I.upper - I.lower‖
    let r := R / (2 : ℝ) ^ p.length
    (volume (Metric.closedBall x r)).toReal ≤
      ((2 * R) ^ d / (volume (I : Set (Vec d))).toReal) *
        (volume (dyadicDescendant I p : Set (Vec d))).toReal := by
  dsimp only
  exact (volume_closedBall_dyadicDescendant_ratio I p x hx hd).le

end

end PDE
