module

public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Essential infimum facts for the weak Harnack step
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace PDE.DGNMMoser

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `(ess inf f)⁻¹ ≤ ess sup f⁻¹` in `ℝ≥0∞`. -/
theorem inv_essInf_le_essSup_inv (f : α → ℝ≥0∞) :
    (essInf f μ)⁻¹ ≤ essSup (fun x => (f x)⁻¹) μ := by
  set S := essSup (fun x => (f x)⁻¹) μ
  have h : ∀ᵐ x ∂μ, S⁻¹ ≤ f x := by
    filter_upwards [ENNReal.ae_le_essSup (fun x => (f x)⁻¹) (μ := μ)] with x hx
    exact ENNReal.inv_le_iff_inv_le.1 hx
  have := le_essInf_of_ae_le (μ := μ) S⁻¹ h
  exact ENNReal.inv_le_iff_inv_le.1 this

/-- If `μ {f < t} ≠ 0`, then `ess inf f ≤ t`. -/
theorem essInf_le_of_measure_lt_ne_zero {f : α → ℝ≥0∞} {t : ℝ≥0∞}
    (h : μ {x | f x < t} ≠ 0) : essInf f μ ≤ t := by
  by_contra hlt
  push Not at hlt
  apply h
  have := ae_essInf_le (f := f) (μ := μ)
  rw [ae_iff] at this
  refine measure_mono_null (fun x hx => ?_) this
  have hx' : f x < t := hx
  exact not_le.2 (hx'.trans hlt)

/-- If `ess inf f < t` then `{f < t}` has positive measure. -/
theorem measure_lt_ne_zero_of_essInf_lt {f : α → ℝ≥0∞} {t : ℝ≥0∞} (h : essInf f μ < t) :
    μ {x | f x < t} ≠ 0 := by
  intro h0
  have hae : ∀ᵐ x ∂μ, t ≤ f x := by
    rw [ae_iff]
    simpa using h0
  exact absurd (le_essInf_of_ae_le (μ := μ) t hae) (not_le.2 h)

/-- `ess inf (f + c) ≤ ess inf f + c`. -/
theorem essInf_add_const_le (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    essInf (fun x => f x + c) μ ≤ essInf f μ + c := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hb
  have hc : c ≠ ⊤ := ne_top_of_le_ne_top hb.ne (le_add_self)
  have hs : essInf f μ ≠ ⊤ := ne_top_of_le_ne_top hb.ne le_self_add
  have hlt : essInf f μ < essInf f μ + ε := ENNReal.lt_add_right hs (by simpa using hε.ne')
  have hne := measure_lt_ne_zero_of_essInf_lt hlt
  have hset : μ {x | f x + c < essInf f μ + ε + c} ≠ 0 := by
    convert hne using 2
    ext x
    simp only [Set.mem_ofPred_eq]
    exact ENNReal.add_lt_add_iff_right hc
  calc essInf (fun x => f x + c) μ ≤ essInf f μ + ε + c :=
        essInf_le_of_measure_lt_ne_zero hset
    _ = essInf f μ + c + ε := by rw [add_right_comm]

end PDE.DGNMMoser
