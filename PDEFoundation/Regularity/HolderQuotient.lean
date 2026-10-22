module

public import PDEFoundation.Regularity.Holder

/-! # Hölder estimates for a scalar quotient with denominator at least one -/

@[expose] public section

namespace PDE

/-- A factor-free difference bound for division by positive denominators
bounded below by one. -/
theorem abs_div_sub_div_le_of_one_le
    {fx fy gx gy : ℝ} (hgx : 1 ≤ gx) (hgy : 1 ≤ gy) :
    |fx / gx - fy / gy| ≤ |fx - fy| + |fy| * |gx - gy| := by
  have hx : 0 < gx := lt_of_lt_of_le (by norm_num) hgx
  have hy : 0 < gy := lt_of_lt_of_le (by norm_num) hgy
  have hprod : 1 ≤ gx * gy := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ gx * gy := mul_le_mul hgx hgy (by norm_num) hx.le
  have hid : fx / gx - fy / gy =
      (fx - fy) / gx + fy * (gy - gx) / (gx * gy) := by
    field_simp [hx.ne', hy.ne']
    ring
  calc
    |fx / gx - fy / gy| = |(fx - fy) / gx + fy * (gy - gx) / (gx * gy)| := by rw [hid]
    _ ≤ |(fx - fy) / gx| + |fy * (gy - gx) / (gx * gy)| := abs_add_le _ _
    _ = |fx - fy| / gx + (|fy| * |gy - gx|) / (gx * gy) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hx, abs_of_pos (mul_pos hx hy)]
    _ ≤ |fx - fy| + |fy| * |gy - gx| :=
      add_le_add (div_le_self (abs_nonneg _) hgx)
        (div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hprod)
    _ = _ := by rw [abs_sub_comm gy gx]

/-- A bounded numerator and a denominator bounded below by one give the
literal scalar quotient Hölder bound. -/
theorem euclideanHolderSeminormLE_div_of_one_le
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ} {α Kf Kg B : ℝ}
    (hf : EuclideanHolderSeminormLE U f α Kf)
    (hg : EuclideanHolderSeminormLE U g α Kg)
    (hB : 0 ≤ B)
    (hbound : ∀ x ∈ U, |f x| ≤ B) (hlower : ∀ x ∈ U, 1 ≤ g x) :
    EuclideanHolderSeminormLE U (fun x => f x / g x) α (Kf + B * Kg) := by
  intro x hx y hy
  calc
    |f x / g x - f y / g y| ≤ |f x - f y| + |f y| * |g x - g y| :=
      abs_div_sub_div_le_of_one_le (hlower x hx) (hlower y hy)
    _ ≤ Kf * vecEuclideanNorm (x - y) ^ α +
        B * (Kg * vecEuclideanNorm (x - y) ^ α) :=
      add_le_add (hf x hx y hy)
        (mul_le_mul (hbound y hy) (hg x hx y hy) (abs_nonneg _)
          hB)
    _ = _ := by ring

end PDE
