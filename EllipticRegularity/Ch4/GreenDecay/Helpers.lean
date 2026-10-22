module

public import EllipticRegularity.Ch4.GreenDecay.LocalBound

/-!
# Real-number bookkeeping for `L²` norms on balls and annuli

* `integral_mul_le_sqrt`: Cauchy--Schwarz for the integral of a product of two `L²` functions.
* `toReal_eLpMeanNormOn_two`: the normalized `L̲²` norm as a real square root.
* `setIntegral_indicator_eq`: integrating an indicator over a larger set.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE

noncomputable section

variable {d : ℕ}

/-- **Cauchy--Schwarz** for `L²` functions on `U`. -/
theorem integral_mul_le_sqrt {U : Set (Vec d)} {f g : Vec d → ℝ} (hf : MemL2On U f)
    (hg : MemL2On U g) :
    (∫ x in U, f x * g x) ≤ Real.sqrt (∫ x in U, f x ^ 2) * Real.sqrt (∫ x in U, g x ^ 2) := by
  rw [integral_mul_eq_inner hf hg.toScalarLp hg.coeFn_toScalarLp]
  refine (real_inner_le_norm _ _).trans ?_
  have e1 : ‖hf.toScalarLp‖ = Real.sqrt (∫ x in U, f x ^ 2) := by
    rw [← toReal_eLpNorm_sq hf]
    rw [Real.sqrt_sq ENNReal.toReal_nonneg]
    exact Lp.norm_toLp f hf
  have e2 : ‖hg.toScalarLp‖ = Real.sqrt (∫ x in U, g x ^ 2) := by
    rw [← toReal_eLpNorm_sq hg]
    rw [Real.sqrt_sq ENNReal.toReal_nonneg]
    exact Lp.norm_toLp g hg
  rw [e1, e2]

/-- The extended `L²` norm as a real square root of the integral of the square. -/
theorem toReal_eLpNorm_two_eq_sqrt {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemL2On U f) :
    (eLpNorm f 2 (volumeOn U)).toReal = Real.sqrt (∫ x in U, f x ^ 2) := by
  rw [← toReal_eLpNorm_sq hf, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- The normalized `L̲²` norm as a real square root. -/
theorem toReal_eLpMeanNormOn_two {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemL2On U f)
    (hUTop : volume U < ∞) :
    (eLpMeanNormOn U 2 f).toReal =
      Real.sqrt ((∫ x in U, f x ^ 2) / (volume U).toReal) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUTop, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_inv, eLpNormOn, toReal_eLpNorm_two_eq_sqrt hf]
  have h12 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
  have hI : 0 ≤ ∫ x in U, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hV : 0 ≤ ((volume U).toReal)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  rw [h12, Real.sqrt_eq_rpow (∫ x in U, f x ^ 2), Real.sqrt_eq_rpow, ← Real.mul_rpow hV hI,
    div_eq_inv_mul]
  congr 1
  rw [inv_mul_eq_div]

/-- Integrating an indicator of a measurable subset over a larger set. -/
theorem setIntegral_indicator_eq {U S : Set (Vec d)} (hS : MeasurableSet S) (hSU : S ⊆ U)
    (f : Vec d → ℝ) : (∫ x in U, S.indicator f x) = ∫ x in S, f x := by
  rw [setIntegral_indicator hS, Set.inter_eq_right.mpr hSU]

end

end PDE.Ch4GreenDecay
