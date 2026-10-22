module

public import PDEFoundation.Analysis.DyadicRadius

/-! # Real-power identities for dyadic oscillation weights -/

@[expose] public section

namespace PDE

noncomputable section

/-- A real power of a dyadic radius splits into its initial-scale and dyadic
factors. -/
theorem dyadicRadius_rpow_eq {R : ℝ} (hR : 0 < R) (α : ℝ) :
    ∀ n : ℕ, dyadicRadius R n ^ α =
      R ^ α * ((2 : ℝ) ^ (-α)) ^ n
  | 0 => by simp
  | n + 1 => by
      have hrn : 0 ≤ dyadicRadius R n := (dyadicRadius_pos hR n).le
      rw [dyadicRadius_succ, Real.div_rpow hrn (by norm_num),
        dyadicRadius_rpow_eq hR α n, pow_succ,
        Real.rpow_neg (by norm_num)]
      field_simp

/-- The scale ratio to a dyadic radius is exactly the corresponding power of
two. -/
theorem div_dyadicRadius_rpow_eq {R : ℝ} (hR : 0 < R) (α : ℝ) (n : ℕ) :
    (R / dyadicRadius R n) ^ α = ((2 : ℝ) ^ α) ^ n := by
  have hrn : dyadicRadius R n = R / (2 : ℝ) ^ n := rfl
  rw [hrn]
  have hR0 : R ≠ 0 := hR.ne'
  have htwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hratio : R / (R / (2 : ℝ) ^ n) = (2 : ℝ) ^ n := by field_simp
  rw [hratio]
  calc
    ((2 : ℝ) ^ n) ^ α = (2 : ℝ) ^ ((n : ℝ) * α) := by
      rw [← Real.rpow_natCast (2 : ℝ) n]
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ (α * (n : ℝ)) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ α) ^ n := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_natCast]

/-- The shrinking-radius factor and the growing oscillation weight cancel. -/
theorem two_rpow_neg_mul_div_dyadicRadius_rpow {R : ℝ} (hR : 0 < R)
    (α : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ (-α)) ^ n * (R / dyadicRadius R n) ^ α = 1 := by
  rw [div_dyadicRadius_rpow_eq hR α n, ← mul_pow]
  have hcancel : (2 : ℝ) ^ (-α) * (2 : ℝ) ^ α = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [hcancel, one_pow]

/-- The oscillation weight gains one factor `2^α` at each dyadic step. -/
theorem div_dyadicRadius_succ_rpow_eq {R : ℝ} (hR : 0 < R)
    (α : ℝ) (n : ℕ) :
    (R / dyadicRadius R (n + 1)) ^ α =
      (2 : ℝ) ^ α * (R / dyadicRadius R n) ^ α := by
  rw [div_dyadicRadius_rpow_eq hR α, div_dyadicRadius_rpow_eq hR α, pow_succ]
  ring

/-- The next oscillation weight cancels the current radius power, leaving one
factor `2^α` at the initial scale. -/
theorem div_dyadicRadius_succ_rpow_mul_current_rpow {R : ℝ} (hR : 0 < R)
    (α : ℝ) (n : ℕ) :
    (R / dyadicRadius R (n + 1)) ^ α * dyadicRadius R n ^ α =
      (2 : ℝ) ^ α * R ^ α := by
  rw [div_dyadicRadius_succ_rpow_eq hR α n,
    div_dyadicRadius_rpow_eq hR α n, dyadicRadius_rpow_eq hR α n]
  have hcancel := two_rpow_neg_mul_div_dyadicRadius_rpow hR α n
  rw [div_dyadicRadius_rpow_eq hR α n] at hcancel
  calc
    _ = (2 : ℝ) ^ α * R ^ α *
        (((2 : ℝ) ^ (-α)) ^ n * ((2 : ℝ) ^ α) ^ n) := by ring
    _ = _ := by rw [hcancel]; ring

end

end PDE
