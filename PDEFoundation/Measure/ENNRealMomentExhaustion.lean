module

public import PDEFoundation.Measure.CappedENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Exhausting extended nonnegative moments by finite caps

Positive real powers of finite real caps increase to the corresponding power
of the original extended nonnegative function, including at infinite values.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The extended nonnegative `q`-moment is the supremum of the moments of the
positive natural caps. No finiteness assumption is needed. -/
theorem lintegral_rpow_eq_iSup_cappedENNReal
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ≥0∞) (hF : Measurable F) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, (F x) ^ q ∂μ) =
      ⨆ n : ℕ,
        ∫⁻ x, ENNReal.ofReal
          ((cappedENNReal (F x) ((n + 1 : ℕ) : NNReal)) ^ q) ∂μ := by
  let f : ℕ → α → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal ((cappedENNReal (F x) ((n + 1 : ℕ) : NNReal)) ^ q)
  have hf (n : ℕ) : Measurable (f n) := by
    apply ENNReal.continuous_ofReal.measurable.comp
    exact (Real.continuous_rpow_const hq.le).measurable.comp
      (PDE.Measurable.cappedENNReal hF _)
  have hmono : Monotone f := by
    intro n m hnm x
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (cappedENNReal_nonneg _ _)
      (cappedENNReal_mono_right (F x) (by exact_mod_cast Nat.add_le_add_right hnm 1)) hq.le
  have hpoint (x : α) : (⨆ n : ℕ, f n x) = (F x) ^ q := by
    simp only [f]
    simp_rw [← ENNReal.ofReal_rpow_of_nonneg
      (cappedENNReal_nonneg (F x) _) hq.le]
    calc
      (⨆ n : ℕ,
          ENNReal.ofReal (cappedENNReal (F x) ((n + 1 : ℕ) : NNReal)) ^ q) =
          (ENNReal.orderIsoRpow q hq)
            (⨆ n : ℕ,
              ENNReal.ofReal (cappedENNReal (F x) ((n + 1 : ℕ) : NNReal))) := by
        rw [(ENNReal.orderIsoRpow q hq).map_iSup]
        simp only [ENNReal.orderIsoRpow_apply]
      _ = (F x) ^ q := by
        rw [iSup_ofReal_cappedENNReal_nat]
        exact ENNReal.orderIsoRpow_apply q hq (F x)
  calc
    (∫⁻ x, (F x) ^ q ∂μ) = ∫⁻ x, ⨆ n : ℕ, f n x ∂μ := by
      congr 1
      funext x
      exact (hpoint x).symm
    _ = ⨆ n : ℕ, ∫⁻ x, f n x ∂μ := lintegral_iSup hf hmono
    _ = _ := rfl

/-- A uniform bound for every finite cap bounds the full extended moment. -/
theorem lintegral_rpow_le_of_cappedENNReal
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ≥0∞) (hF : Measurable F) {q : ℝ} (hq : 0 < q)
    {K : ℝ≥0∞}
    (hK : ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal
        ((cappedENNReal (F x) ((n + 1 : ℕ) : NNReal)) ^ q) ∂μ) ≤ K) :
    (∫⁻ x, (F x) ^ q ∂μ) ≤ K := by
  rw [lintegral_rpow_eq_iSup_cappedENNReal μ F hF hq]
  exact iSup_le hK

end PDE
