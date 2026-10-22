module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ACF-A: the AM--GM step over abstract reals

With `J ≤ r⁻ⁿ (√(ab) + n a / (2r))` and `b + t (t + n) r⁻² a ≤ c` one gets
`2 t J ≤ r (r⁻ⁿ c)`.
-/

@[expose] public section

namespace PDE

namespace ACFAssembly

theorem amgm_step {r a b c t J : ℝ} {n : ℕ} (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hW : J ≤ (r ^ n)⁻¹ * (Real.sqrt (a * b) + (n : ℝ) * a / (2 * r)))
    (hS : b + t * (t + (n : ℝ)) * (r ^ 2)⁻¹ * a ≤ c) :
    2 * t * J ≤ r * ((r ^ n)⁻¹ * c) := by
  have hP : 0 < (r ^ n)⁻¹ := by positivity
  set s := Real.sqrt (a * b) with hs
  have hs' : s = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsq : 0 ≤ (r * Real.sqrt b - t * Real.sqrt a) ^ 2 := sq_nonneg _
  have h1 : 2 * t * r * s ≤ r ^ 2 * b + t ^ 2 * a := by
    rw [hs']; nlinarith only [hsq, hsa, hsb]
  have h2 : 2 * t * s + t * n * a / r ≤ r * c := by
    have hrc : r * (b + t * (t + n) * (r ^ 2)⁻¹ * a) ≤ r * c :=
      mul_le_mul_of_nonneg_left hS hr.le
    have e : r * (b + t * (t + n) * (r ^ 2)⁻¹ * a) =
        (r ^ 2 * b + t ^ 2 * a + t * n * a) / r := by
      field_simp
      ring
    have e2 : 2 * t * s + t * n * a / r = (2 * t * r * s + t * n * a) / r := by
      field_simp
    rw [e2]
    refine le_trans ?_ (e ▸ hrc)
    exact div_le_div_of_nonneg_right (by linarith only [h1]) hr.le
  calc 2 * t * J ≤ 2 * t * ((r ^ n)⁻¹ * (s + (n : ℝ) * a / (2 * r))) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (r ^ n)⁻¹ * (2 * t * s + t * n * a / r) := by
        field_simp
    _ ≤ (r ^ n)⁻¹ * (r * c) := mul_le_mul_of_nonneg_left h2 hP.le
    _ = r * ((r ^ n)⁻¹ * c) := by ring

end ACFAssembly

end PDE
