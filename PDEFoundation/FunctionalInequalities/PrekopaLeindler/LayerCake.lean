module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Layer-cake formula for `[0,∞]`-valued measurable functions

`∫⁻ f ∂μ = ∫⁻ t in Ioi 0, μ {x | ofReal t < f x}`.
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal

/-- The one-variable layer: `∫⁻ t in Ioi 0, 1[t < c] = c`. -/
theorem lintegral_Ioi_indicator_lt (c : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < c}.indicator 1 t = c := by
  have hS : MeasurableSet {t : ℝ | ENNReal.ofReal t < c} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [lintegral_indicator_one hS, Measure.restrict_apply hS]
  rcases eq_or_ne c ∞ with rfl | hc
  · have : {t : ℝ | ENNReal.ofReal t < ∞} ∩ Ioi 0 = Ioi 0 := by
      ext t; simp
    rw [this]; simp
  · have : {t : ℝ | ENNReal.ofReal t < c} ∩ Ioi 0 = Ioo 0 c.toReal := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le hc).1 h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h2.le hc).2 h1, h2⟩
    rw [this, Real.volume_Ioo]; simp [hc]

/-- Layer-cake formula for `[0,∞]`-valued measurable functions. -/
theorem lintegral_eq_lintegral_meas_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
  have hS : MeasurableSet {p : α × ℝ | ENNReal.ofReal p.2 < f p.1} :=
    measurableSet_lt (by fun_prop) (hf.comp measurable_fst)
  have hmeas : Measurable (Function.uncurry fun (x : α) (t : ℝ) =>
      {t : ℝ | ENNReal.ofReal t < f x}.indicator (1 : ℝ → ℝ≥0∞) t) := by
    have h2 := (measurable_const (a := (1 : ℝ≥0∞)) : Measurable fun _ : α × ℝ => (1 : ℝ≥0∞)).indicator hS
    convert h2 using 1
    ext p
    simp [Set.indicator, Function.uncurry]
  calc ∫⁻ x, f x ∂μ
      = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < f x}.indicator 1 t) ∂μ := by
        congr 1; ext x; exact (lintegral_Ioi_indicator_lt (f x)).symm
    _ = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ x, {t : ℝ | ENNReal.ofReal t < f x}.indicator 1 t ∂μ) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
        congr 1; ext t
        have hT : MeasurableSet {x | ENNReal.ofReal t < f x} :=
          measurableSet_lt measurable_const hf
        have : (fun x => {t' : ℝ | ENNReal.ofReal t' < f x}.indicator (1 : ℝ → ℝ≥0∞) t) =
            {x | ENNReal.ofReal t < f x}.indicator 1 := by
          ext x; simp [Set.indicator]
        rw [this, lintegral_indicator_one hT]

/-- Layer-cake formula on `ℝ` with Lebesgue measure. -/
theorem lintegral_eq_lintegral_volume_lt {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < f x} :=
  lintegral_eq_lintegral_meas_lt hf

end PDE.PrekopaLeindlerProof
