module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Exact norm of the nonnegative dual power -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The dual power of a nonnegative measurable real function is measurable. -/
theorem measurable_nonnegativeDualPower
    {f : α → ℝ} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    Measurable (fun x => f x ^ (p - 1)) :=
  (Real.continuous_rpow_const (sub_nonneg.mpr hp.le)).measurable.comp hf

/-- Exact dual-exponent norm of the nonnegative power `f ^ (p - 1)`. -/
theorem eLpNorm_nonnegativeDualPower
    {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun x => f x ^ (p - 1))
        (ENNReal.ofReal (p / (p - 1))) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
  have hpSub : 0 < p - 1 := sub_pos.mpr hp
  have hq0 : 0 ≤ p / (p - 1) :=
    div_nonneg (zero_le_one.trans hp.le) hpSub.le
  have hexp : ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) =
      ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul hq0]
    congr 1
    field_simp
  have hfun : (fun x => f x ^ (p - 1)) = fun x => ‖f x‖ ^ (p - 1) := by
    funext x
    rw [Real.norm_of_nonneg (hf0 x)]
  by_cases hfm : AEStronglyMeasurable f μ
  · rw [hfun, eLpNorm_norm_rpow f hfm hpSub, hexp]
  · have hpow : ¬ AEStronglyMeasurable (fun x => f x ^ (p - 1)) μ := by
      intro h
      apply hfm
      have h' := (Real.continuous_rpow_const (inv_nonneg.mpr hpSub.le)).comp_aestronglyMeasurable h
      refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
      exact Real.rpow_rpow_inv (hf0 x) hpSub.ne'
    rw [eLpNorm_of_not_aestronglyMeasurable hpow, eLpNorm_of_not_aestronglyMeasurable hfm,
      ENNReal.top_rpow_of_pos hpSub]

/-- A nonnegative `Lᵖ` function has its literal dual power in `Lᑫ`, with the
exact expected norm. -/
theorem memLp_nonnegativeDualPower
    {f : α → ℝ} (_hfMeas : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun x => f x ^ (p - 1))
      (ENNReal.ofReal (p / (p - 1))) μ := by
  rw [memLp_iff, eLpNorm_nonnegativeDualPower hf0 hp]
  exact ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hp.le)
    hf.eLpNorm_lt_top.ne

end

end PDE
