module

public import Mathlib.MeasureTheory.Function.EssSup

/-! # Extracting an essential-infimum affine bound -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- An almost everywhere affine lower bound by a nonnegative real function
descends to the essential infimum of that function. -/
theorem ofReal_le_add_mul_essInf_of_ae
    (μ : Measure α) (b : α → ℝ) (e A B : ℝ)
    (hb : ∀ᵐ x ∂μ, 0 ≤ b x) (_he : 0 ≤ e) (hA : 0 ≤ A) (hB : 0 < B)
    (hbound : ∀ᵐ x ∂μ,
      ENNReal.ofReal e ≤
        ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (b x)) :
    ENNReal.ofReal e ≤ ENNReal.ofReal A +
      ENNReal.ofReal B * essInf (fun x => ENNReal.ofReal (b x)) μ := by
  by_cases heA : e ≤ A
  · exact (ENNReal.ofReal_le_ofReal heA).trans
      (le_add_of_nonneg_right (mul_nonneg (zero_le) (zero_le)))
  · have hAe : A < e := lt_of_not_ge heA
    let c : ℝ := (e - A) / B
    have hc : 0 < c := div_pos (sub_pos.mpr hAe) hB
    have hcb : ∀ᵐ x ∂μ, c ≤ b x := by
      filter_upwards [hb, hbound] with x hbx hx
      have hreal : e ≤ A + B * b x := by
        rw [← ENNReal.ofReal_le_ofReal_iff
          (add_nonneg hA (mul_nonneg hB.le hbx))]
        simpa only [ENNReal.ofReal_add hA (mul_nonneg hB.le hbx),
          ENNReal.ofReal_mul hB.le] using hx
      dsimp only [c]
      exact (div_le_iff₀ hB).mpr (by linarith)
    have hcess : ENNReal.ofReal c ≤
        essInf (fun x => ENNReal.ofReal (b x)) μ := by
      refine le_essInf_of_ae_le _ ?_
      filter_upwards [hcb] with x hx
      exact ENNReal.ofReal_le_ofReal hx
    have hid : A + B * c = e := by
      dsimp only [c]
      field_simp
      linarith
    calc
      ENNReal.ofReal e =
          ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal c := by
        calc
          ENNReal.ofReal e = ENNReal.ofReal (A + B * c) := congrArg _ hid.symm
          _ = ENNReal.ofReal A + ENNReal.ofReal (B * c) :=
            ENNReal.ofReal_add hA (mul_nonneg hB.le hc.le)
          _ = ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal c := by
            rw [ENNReal.ofReal_mul hB.le]
      _ ≤ ENNReal.ofReal A +
          ENNReal.ofReal B * essInf (fun x => ENNReal.ofReal (b x)) μ :=
        by gcongr

end PDE
