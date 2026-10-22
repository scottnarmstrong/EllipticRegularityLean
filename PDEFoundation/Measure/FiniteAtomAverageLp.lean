module

public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The literal real average of a function on one finite-measure atom. -/
def finiteAtomAverage (μ : Measure α) (E : Set α) (f : α → ℝ) : ℝ :=
  (μ E).toReal⁻¹ * ∫ x in E, f x ∂μ

/-- Averaging on a measurable atom contracts every real `Lᵖ` moment for
`p ≥ 1`, including the zero-measure atom case. -/
theorem measureReal_mul_abs_finiteAtomAverage_rpow_le
    (μ : Measure α) [IsFiniteMeasure μ]
    (E : Set α) (f : α → ℝ)
    {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) (μ.restrict E)) :
    (μ E).toReal * |finiteAtomAverage μ E f| ^ p ≤
      ∫ x in E, |f x| ^ p ∂μ := by
  by_cases hμE : μ E = 0
  · have hzero : (μ E).toReal = 0 := by rw [hμE, ENNReal.toReal_zero]
    rw [hzero, zero_mul]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  · have hμEtop : μ E ≠ ∞ := (measure_lt_top μ E).ne
    let ν : Measure α := (μ E)⁻¹ • μ.restrict E
    have hνuniv : ν Set.univ = 1 := by
      simp only [ν, Measure.smul_apply, Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel hμE hμEtop
    let : IsProbabilityMeasure ν := ⟨hνuniv⟩
    have hscale_ne_top : (μ E)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hμE
    have hfν : MemLp f (ENNReal.ofReal p) ν := hf.smul_measure hscale_ne_top
    have hp0 : 0 < p := zero_lt_one.trans_le hp
    have hfiν : Integrable f ν := hfν.integrable (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hp)
    have hfpν : Integrable (fun x => |f x| ^ p) ν := by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
        hfν.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne'
          ENNReal.ofReal_ne_top
    have hj := abs_integral_rpow_le_integral_abs_rpow hp hfiν hfpν
    have hintν : ∫ x, f x ∂ν = finiteAtomAverage μ E f := by
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_inv, finiteAtomAverage, smul_eq_mul]
    have hpowν : ∫ x, |f x| ^ p ∂ν =
        (μ E).toReal⁻¹ * ∫ x in E, |f x| ^ p ∂μ := by
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_inv, smul_eq_mul]
    rw [hintν, hpowν] at hj
    have hmpos : 0 < (μ E).toReal := ENNReal.toReal_pos hμE hμEtop
    calc
      (μ E).toReal * |finiteAtomAverage μ E f| ^ p ≤
          (μ E).toReal * ((μ E).toReal⁻¹ * ∫ x in E, |f x| ^ p ∂μ) :=
        mul_le_mul_of_nonneg_left hj hmpos.le
      _ = ∫ x in E, |f x| ^ p ∂μ := by
        rw [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul]

end

end PDE
