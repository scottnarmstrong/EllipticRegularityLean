module

public import PDEFoundation.Analysis.HilbertBallAverage
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuous fixed-scale representations of normalized radial averages -/

@[expose] public section

namespace PDE.Internal

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A normalized radial average written on the fixed interval `[0,1]`. -/
def fixedScaleRadialAverage (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  (d : ℝ) * ∫ t in (0 : ℝ)..1, t ^ (d - 1) * F (r * t)

/-- The fixed-scale representation is continuous in the radius. -/
theorem continuous_fixedScaleRadialAverage (F : ℝ → ℝ) (hF : Continuous F) :
    Continuous (fixedScaleRadialAverage (d := d) F) := by
  unfold fixedScaleRadialAverage
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

/-- On positive radii, the fixed-scale representation is the usual
dimension-normalized radial integral. -/
theorem fixedScaleRadialAverage_eq_normalizedRadialIntegral [NeZero d]
    (F : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    fixedScaleRadialAverage (d := d) F r =
      (d : ℝ) / r ^ d * ∫ s in (0 : ℝ)..r, s ^ (d - 1) * F s := by
  have hr0 : r ≠ 0 := hr.ne'
  have hchange := intervalIntegral.integral_comp_mul_right
    (a := (0 : ℝ)) (b := 1) (c := r)
    (fun s : ℝ => s ^ (d - 1) * F s) hr0
  simp only [zero_mul, one_mul] at hchange
  unfold fixedScaleRadialAverage
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hpow : ∀ t : ℝ, (r * t) ^ (d - 1) = r ^ (d - 1) * t ^ (d - 1) :=
    fun t => mul_pow r t (d - 1)
  have hscaled : r ^ (d - 1) *
        ∫ t in (0 : ℝ)..1, t ^ (d - 1) * F (r * t) =
      r⁻¹ * ∫ s in (0 : ℝ)..r, s ^ (d - 1) * F s := by
    rw [← intervalIntegral.integral_const_mul]
    convert hchange using 1
    ring_nf
  have hmain : r ^ d * ∫ t in (0 : ℝ)..1, t ^ (d - 1) * F (r * t) =
      ∫ s in (0 : ℝ)..r, s ^ (d - 1) * F s := by
    have hpowd : r ^ d = r ^ (d - 1) * r := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpowd]
    calc
      r ^ (d - 1) * r * ∫ t in (0 : ℝ)..1, t ^ (d - 1) * F (r * t) =
          r * (r ^ (d - 1) * ∫ t in (0 : ℝ)..1,
            t ^ (d - 1) * F (r * t)) := by ring
      _ = r * (r⁻¹ * ∫ s in (0 : ℝ)..r, s ^ (d - 1) * F s) := by rw [hscaled]
      _ = _ := by field_simp
  field_simp
  simpa only [mul_comm] using hmain

end

end PDE.Internal
