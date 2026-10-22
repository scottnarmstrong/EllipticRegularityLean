module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Cancellation in extended nonnegative moment inequalities -/

@[expose] public section

namespace PDE

open scoped ENNReal

/-- Cancel the finite positive residual moment factor in the algebraic form
arising from a localized distribution estimate. No finiteness of `b` is
required. -/
theorem rpow_le_of_moment_mul_le
    {q : ℝ} (hq : 1 < q) {a b : ℝ≥0∞} (haTop : a ≠ ⊤)
    (h : ENNReal.ofReal (q - 1) * a ≤
      ENNReal.ofReal q * b ^ (1 / q) * a ^ ((q - 1) / q)) :
    a ^ (1 / q) ≤ ENNReal.ofReal (q / (q - 1)) * b ^ (1 / q) := by
  by_cases ha0 : a = 0
  · rw [ha0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr (zero_lt_one.trans hq))]
    exact zero_le
  have hq0 : 0 < q := zero_lt_one.trans hq
  have he : 0 < (q - 1) / q := div_pos (sub_pos.mpr hq) hq0
  let z : ℝ≥0∞ := a ^ ((q - 1) / q)
  have hz0 : z ≠ 0 := by
    rw [ne_eq, ENNReal.rpow_eq_zero_iff]
    simp [ha0, haTop, he.not_gt]
  have hzTop : z ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg he.le haTop
  have haSplit : a = a ^ (1 / q) * z := by
    have hexp : 1 / q + (q - 1) / q = 1 := by
      field_simp
      ring
    rw [← ENNReal.rpow_add (x := a) (1 / q) ((q - 1) / q) ha0 haTop,
      hexp, ENNReal.rpow_one]
  have hfactor :
      (ENNReal.ofReal (q - 1) * a ^ (1 / q)) * z ≤
        (ENNReal.ofReal q * b ^ (1 / q)) * z := by
    calc
      (ENNReal.ofReal (q - 1) * a ^ (1 / q)) * z =
          ENNReal.ofReal (q - 1) * (a ^ (1 / q) * z) := by ac_rfl
      _ = ENNReal.ofReal (q - 1) * a := by rw [← haSplit]
      _ ≤ ENNReal.ofReal q * b ^ (1 / q) * z := by simpa only [z] using h
  have hcancel : ENNReal.ofReal (q - 1) * a ^ (1 / q) ≤
      ENNReal.ofReal q * b ^ (1 / q) :=
    (ENNReal.mul_le_mul_iff_left hz0 hzTop).mp hfactor
  have hqm0 : ENNReal.ofReal (q - 1) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sub_pos.mpr hq)
  have hdiv : a ^ (1 / q) ≤
      (ENNReal.ofReal q * b ^ (1 / q)) / ENNReal.ofReal (q - 1) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hqm0)
      (Or.inl ENNReal.ofReal_ne_top)).2
    simpa only [mul_comm] using hcancel
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hq)]
  calc
    a ^ (1 / q) ≤
        (ENNReal.ofReal q * b ^ (1 / q)) / ENNReal.ofReal (q - 1) := hdiv
    _ = ENNReal.ofReal q / ENNReal.ofReal (q - 1) * b ^ (1 / q) := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ac_rfl

end PDE
