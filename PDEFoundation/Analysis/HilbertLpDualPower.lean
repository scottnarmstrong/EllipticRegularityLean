module

public import PDEFoundation.Measure.NonnegativeDualPower
public import PDEFoundation.Measure.LpPower
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Dual powers for Hilbert-valued `Lᵖ` functions -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure α}

/-- The literal Hilbert-space dual power of a vector. -/
def hilbertDualPower (r : ℝ) (v : E) : E :=
  (‖v‖ ^ (r - 1) / ‖v‖) • v

omit [MeasurableSpace α] in
/-- The norm of the Hilbert dual power is the expected scalar dual power. -/
theorem norm_hilbertDualPower {r : ℝ} (hr : 1 < r) (v : E) :
    ‖hilbertDualPower r v‖ = ‖v‖ ^ (r - 1) := by
  by_cases hv : ‖v‖ = 0
  · simp [hilbertDualPower, hv, Real.zero_rpow (sub_ne_zero.mpr (ne_of_gt hr))]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    rw [hilbertDualPower, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg hvpos.le _) hvpos.le),
      div_mul_cancel₀ _ hv]

omit [MeasurableSpace α] in
/-- Pairing a vector with its Hilbert dual power gives its `r`th norm power. -/
theorem real_inner_hilbertDualPower {r : ℝ} (hr : 1 < r) (v : E) :
    inner ℝ v (hilbertDualPower r v) = ‖v‖ ^ r := by
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    simp [hv0, hilbertDualPower, Real.zero_rpow (ne_of_gt (zero_lt_one.trans hr))]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    rw [hilbertDualPower, real_inner_smul_right, real_inner_self_eq_norm_sq]
    calc
      ‖v‖ ^ (r - 1) / ‖v‖ * ‖v‖ ^ 2 = ‖v‖ ^ (r - 1) * ‖v‖ := by
        field_simp
      _ = ‖v‖ ^ (r - 1) * ‖v‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖v‖ ^ ((r - 1) + 1) := (Real.rpow_add hvpos _ _).symm
      _ = ‖v‖ ^ r := by congr 1; ring

/-- The Hilbert dual power of an almost-everywhere strongly measurable field
is almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_hilbertDualPower
    {g : α → E} (hg : AEStronglyMeasurable g μ) (r : ℝ) :
    AEStronglyMeasurable (fun x => hilbertDualPower r (g x)) μ := by
  have hn : AEStronglyMeasurable (fun x => ‖g x‖) μ := hg.norm
  have hp : AEStronglyMeasurable (fun x => ‖g x‖ ^ (r - 1)) μ :=
    (hn.aemeasurable.pow_const _).aestronglyMeasurable
  exact ((hp.aemeasurable.div hn.aemeasurable).aestronglyMeasurable).smul hg

/-- A genuine Hilbert-valued `Lʳ` field has a dual power in the conjugate
space, with the exact expected norm. -/
theorem memLp_hilbertDualPower
    {g : α → E} {r : ℝ} (hr : 1 < r)
    (hg : MemLp g (ENNReal.ofReal r) μ) :
    MemLp (fun x => hilbertDualPower r (g x))
      (ENNReal.ofReal (r / (r - 1))) μ ∧
    eLpNorm (fun x => hilbertDualPower r (g x))
        (ENNReal.ofReal (r / (r - 1))) μ =
      eLpNorm g (ENNReal.ofReal r) μ ^ (r - 1) := by
  have hnorm : (fun x => ‖hilbertDualPower r (g x)‖) =
      fun x => ‖g x‖ ^ (r - 1) := by
    funext x
    exact norm_hilbertDualPower hr (g x)
  have hmeas := aestronglyMeasurable_hilbertDualPower hg.aestronglyMeasurable r
  have hnormeq :
      eLpNorm (fun x => hilbertDualPower r (g x))
          (ENNReal.ofReal (r / (r - 1))) μ =
        eLpNorm g (ENNReal.ofReal r) μ ^ (r - 1) := by
    rw [← eLpNorm_norm _ hmeas, hnorm]
    simpa only [eLpNorm_norm _ hg.aestronglyMeasurable] using!
      (eLpNorm_nonnegativeDualPower (μ := μ)
        (fun x => norm_nonneg (g x)) hr)
  exact ⟨(hnormeq.trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hr.le)
      hg.eLpNorm_lt_top.ne)), hnormeq⟩

/-- The integral pairing of a Hilbert-valued `Lʳ` field with its literal dual
power is the `r`th power of its real `Lʳ` norm. -/
theorem integral_real_inner_hilbertDualPower
    {g : α → E} {r : ℝ} (hr : 1 < r)
    (hg : MemLp g (ENNReal.ofReal r) μ) :
    ∫ x, inner ℝ (g x) (hilbertDualPower r (g x)) ∂μ =
      (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r := by
  rw [toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm (zero_lt_one.trans hr) hg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => real_inner_hilbertDualPower hr (g x)

end

end PDE
