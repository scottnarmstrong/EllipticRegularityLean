module

public import PDEFoundation.Geometry.BoxCenter
public import PDEFoundation.Measure.BallVolume

/-! # Volume of the circumscribed round ball of an equal-side box -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set
open scoped ENNReal

/-- The circumscribed round ball to equal-side box volume ratio depends only
on the dimension. -/
theorem volume_euclideanBall_boxCenter_div_box_of_commonWidth
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    (volume (euclideanBall (boxCenter I) (Real.sqrt d * L / 2))).toReal /
        (volume (I : Set (Vec d))).toReal =
      (volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d / 2) ^ d := by
  let i0 : Fin d := ⟨0, hd⟩
  have hL : 0 < L := by
    rw [← hwidth i0]
    exact sub_pos.mpr (I.lower_lt_upper i0)
  have hr : 0 < Real.sqrt d * L / 2 := by
    have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    positivity
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hr,
    volume_box_toReal_eq_pow_of_commonWidth I L hwidth]
  have hLpow : L ^ d ≠ 0 := pow_ne_zero _ hL.ne'
  rw [show Real.sqrt d * L / 2 = (Real.sqrt d / 2) * L by ring, mul_pow]
  field_simp

/-- Square-root form of the dimension-only circumscribed ball to box volume
ratio. -/
theorem sqrt_volume_euclideanBall_boxCenter_div_box_of_commonWidth
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L) :
    Real.sqrt ((volume
        (euclideanBall (boxCenter I) (Real.sqrt d * L / 2))).toReal /
      (volume (I : Set (Vec d))).toReal) =
    Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      (Real.sqrt d / 2) ^ d) := by
  rw [volume_euclideanBall_boxCenter_div_box_of_commonWidth I L hd hwidth]

/-- Every literal dyadic descendant has the same circumscribed ball to box
volume ratio as its equal-side root. -/
theorem volume_euclideanBall_boxCenter_dyadicDescendant_div
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (p : List (Set (Fin d))) :
    (volume (euclideanBall (boxCenter (dyadicDescendant I p))
      (Real.sqrt d * (L / (2 : ℝ) ^ p.length) / 2))).toReal /
        (volume (dyadicDescendant I p : Set (Vec d))).toReal =
      (volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d / 2) ^ d := by
  apply volume_euclideanBall_boxCenter_div_box_of_commonWidth
    (dyadicDescendant I p) (L / (2 : ℝ) ^ p.length) hd
  exact upper_sub_lower_dyadicDescendant_of_commonWidth I L hwidth p

/-- Circumscribed radii scale by the reciprocal dyadic path factor. -/
theorem boxCenter_circumscribedRadius_dyadicDescendant_div
    {d : ℕ} (I : Box (Fin d)) (L : ℝ) (hd : 0 < d)
    (hwidth : ∀ i, I.upper i - I.lower i = L)
    (p : List (Set (Fin d))) :
    (Real.sqrt d * (L / (2 : ℝ) ^ p.length) / 2) /
        (Real.sqrt d * L / 2) =
      1 / (2 : ℝ) ^ p.length := by
  let i0 : Fin d := ⟨0, hd⟩
  have hL : L ≠ 0 := by
    have : 0 < L := by
      rw [← hwidth i0]
      exact sub_pos.mpr (I.lower_lt_upper i0)
    exact this.ne'
  have hsqrt : Real.sqrt d ≠ 0 := by
    exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'
  field_simp

/-- The open interior of a box has positive Lebesgue volume. -/
theorem volume_box_Ioo_pos {d : ℕ} (I : Box (Fin d)) :
    0 < volume (Box.Ioo I) := by
  rw [← (Box.coe_ae_eq_Ioo I).measure_eq]
  apply (ENNReal.toReal_pos_iff.mp ?_).1
  rw [Box.volume_apply']
  exact Finset.prod_pos fun i _ => sub_pos.mpr (I.lower_lt_upper i)

/-- The open interior of a box has finite Lebesgue volume. -/
theorem volume_box_Ioo_lt_top {d : ℕ} (I : Box (Fin d)) :
    volume (Box.Ioo I) < ∞ := by
  rw [← (Box.coe_ae_eq_Ioo I).measure_eq]
  exact I.measure_coe_lt_top volume

end PDE
