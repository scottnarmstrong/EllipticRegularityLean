module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Exact power cancellation in extended nonnegative inequalities -/

@[expose] public section

namespace PDE

open scoped ENNReal

/-- Cancel the finite positive residual power in a moment inequality.  The
coefficient may be infinite. -/
theorem ENNReal.rpow_one_div_le_of_le_mul_rpow
    {p : ℝ} (hp : 1 < p) {a K : ℝ≥0∞} (haTop : a ≠ ⊤)
    (h : a ≤ K * a ^ ((p - 1) / p)) :
    a ^ (1 / p) ≤ K := by
  by_cases ha0 : a = 0
  · rw [ha0, ENNReal.zero_rpow_of_pos
      (one_div_pos.mpr (zero_lt_one.trans hp))]
    exact zero_le
  have hp0 : 0 < p := zero_lt_one.trans hp
  have he : 0 < (p - 1) / p := div_pos (sub_pos.mpr hp) hp0
  let z : ℝ≥0∞ := a ^ ((p - 1) / p)
  have hz0 : z ≠ 0 := by
    rw [ne_eq, ENNReal.rpow_eq_zero_iff]
    simp [ha0, haTop, he.not_gt]
  have hzTop : z ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg he.le haTop
  have haSplit : a = a ^ (1 / p) * z := by
    have hexp : 1 / p + (p - 1) / p = 1 := by
      field_simp
      ring
    rw [← ENNReal.rpow_add (x := a) (1 / p) ((p - 1) / p) ha0 haTop,
      hexp, ENNReal.rpow_one]
  apply (ENNReal.mul_le_mul_iff_right hz0 hzTop).mp
  rw [mul_comm z (a ^ (1 / p)), mul_comm z K, ← haSplit]
  exact h

end PDE
