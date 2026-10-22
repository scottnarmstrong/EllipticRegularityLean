module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of superlevel tails of `L^q` functions

A function in `L^q`, for finite `q > 1`, is integrable after restriction to
any positive superlevel set, without a finite ambient measure assumption.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- Above a positive threshold, a first power is controlled by a `q`th power
with the explicit threshold factor. -/
theorem le_rpow_mul_rpow_of_lt
    {a s q : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hq : 1 < q) (hsa : s < a) :
    a ≤ s ^ (1 - q) * a ^ q := by
  have hexp : 0 ≤ q - 1 := by linarith
  have hpow : s ^ (q - 1) ≤ a ^ (q - 1) :=
    Real.rpow_le_rpow hs.le hsa.le hexp
  have haPos : 0 < a := hs.trans hsa
  have hsPow : 0 < s ^ (q - 1) := Real.rpow_pos_of_pos hs _
  have hmul : a * s ^ (q - 1) ≤ a ^ q := by
    calc
      a * s ^ (q - 1) ≤ a * a ^ (q - 1) :=
        mul_le_mul_of_nonneg_left hpow ha
      _ = a ^ (1 : ℝ) * a ^ (q - 1) := by simp only [Real.rpow_one]
      _ = a ^ ((1 : ℝ) + (q - 1)) :=
        (Real.rpow_add haPos 1 (q - 1)).symm
      _ = a ^ q := by ring_nf
  rw [show 1 - q = -(q - 1) by ring, Real.rpow_neg hs.le,
    inv_mul_eq_div]
  exact (le_div_iff₀ hsPow).mpr hmul

/-- The part of an `L^q` real function above a positive absolute-value
threshold is integrable, even when the ambient measure is infinite. -/
theorem integrable_indicator_abs_gt_of_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b : α → ℝ) {q s : ℝ} (hq : 1 < q) (hs : 0 < s)
    (hb : MemLp b (ENNReal.ofReal q) μ) :
    Integrable ({x | s < |b x|}.indicator b) μ := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hpower : Integrable (fun x => |b x| ^ q) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using
      hb.integrable_norm_rpow
        (by
          intro h
          rw [ENNReal.ofReal_eq_zero] at h
          exact (not_le_of_gt hq0) h)
        ENNReal.ofReal_ne_top
  have hdom : Integrable (fun x => s ^ (1 - q) * |b x| ^ q) μ :=
    hpower.const_mul _
  have habsMeas : AEMeasurable (fun x => |b x|) μ := by
    simpa only [Real.norm_eq_abs] using
      hb.aestronglyMeasurable.norm.aemeasurable
  have hset : NullMeasurableSet {x | s < |b x|} μ := by
    exact habsMeas.nullMeasurableSet_preimage measurableSet_Ioi
  apply hdom.mono' (hb.aestronglyMeasurable.indicator₀ hset)
  filter_upwards [] with x
  by_cases hx : x ∈ {x | s < |b x|}
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
    exact le_rpow_mul_rpow_of_lt (abs_nonneg (b x)) hs hq hx
  · simp only [Set.indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hs.le _)
      (Real.rpow_nonneg (abs_nonneg (b x)) _)

end PDE
