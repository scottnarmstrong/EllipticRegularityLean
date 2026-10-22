module

public import PDEFoundation.Measure.BoxCircumscribedBallVolume

@[expose] public section

namespace PDE

open MeasureTheory

/-- Exact gap power in the retained-cube energy bound. -/
lemma sqrt_two_div_pow_eq (d : ℕ) {h : ℝ} (hh : 0 < h) :
    Real.sqrt ((2 / h) ^ d) =
      (2 : ℝ) ^ ((d : ℝ) / 2) * h ^ (-(d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (div_nonneg (by norm_num) hh.le)]
  rw [show (d : ℝ) * (1 / 2) = (d : ℝ) / 2 by ring,
    Real.div_rpow (by norm_num) hh.le]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg hh.le, div_eq_mul_inv]

/-- The circumscribed-volume factor times the doubled-ball factor is exactly
the manuscript's `V_d`. -/
lemma circumscribedVolumeFactor_mul_sqrt_two_pow (d : ℕ) :
    Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      (Real.sqrt d / 2) ^ d) * Real.sqrt ((2 : ℝ) ^ d) =
    Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
      (Real.sqrt d) ^ d) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp

/-- Natural powers under the square root agree exactly with half-dimensional
real powers. -/
lemma sqrt_two_pow_eq_rpow_half (d : ℕ) :
    Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- The sparse coefficient times the volume ratio is exactly `2 V_d`. -/
lemma sparseDominationConstant_mul_circumscribedVolumeFactor (d : ℕ) :
    (2 : ℝ) ^ (1 + (d : ℝ) / 2) *
        Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
          (Real.sqrt d / 2) ^ d) =
      2 * Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d) ^ d) := by
  have hV := circumscribedVolumeFactor_mul_sqrt_two_pow d
  rw [sqrt_two_pow_eq_rpow_half] at hV
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  calc
    _ = 2 * (Real.sqrt ((volume (euclideanBall (0 : Vec d) 1)).toReal *
        (Real.sqrt d / 2) ^ d) * (2 : ℝ) ^ ((d : ℝ) / 2)) := by ring
    _ = _ := by rw [hV]

/-- The dyadic-domination coefficient has the exact real-power factor used
in the local energy constant. -/
lemma two_mul_sparseDominationConstant (d : ℕ) :
    2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) =
      (2 : ℝ) ^ (2 + (d : ℝ) / 2) := by
  conv_rhs =>
    rw [show 2 + (d : ℝ) / 2 = 1 + (1 + (d : ℝ) / 2) by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]

end PDE
