module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurable minorants and majorants of a.e.-measurable `[0,∞]`-valued functions
-/

@[expose] public section

namespace PDE.PrekopaLeindlerProof

open MeasureTheory Set
open scoped ENNReal

/-- An a.e.-measurable function has a measurable minorant that agrees with it almost everywhere. -/
theorem exists_measurable_le_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∃ F : α → ℝ≥0∞, Measurable F ∧ F ≤ f ∧ F =ᵐ[μ] f := by
  classical
  set T := toMeasurable μ {x | f x ≠ hf.mk f x} with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : μ T = 0 := by
    rw [hT, measure_toMeasurable]; exact hf.ae_eq_mk
  refine ⟨Tᶜ.indicator (hf.mk f), hf.measurable_mk.indicator hTm.compl, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ T
    · simp [hx]
    · have : f x = hf.mk f x := by
        by_contra h
        exact hx (subset_toMeasurable _ _ h)
      simp [hx, this]
  · have : ∀ᵐ x ∂μ, x ∉ T := by
      rw [ae_iff]; simpa using hT0
    filter_upwards [this, hf.ae_eq_mk] with x hx hx'
    simp [hx, hx']

/-- An a.e.-measurable function has a measurable majorant that agrees with it almost
everywhere. -/
theorem exists_measurable_ge_ae_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∃ K : α → ℝ≥0∞, Measurable K ∧ f ≤ K ∧ K =ᵐ[μ] f := by
  classical
  set T := toMeasurable μ {x | f x ≠ hf.mk f x} with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : μ T = 0 := by
    rw [hT, measure_toMeasurable]; exact hf.ae_eq_mk
  refine ⟨T.piecewise (fun _ => ∞) (hf.mk f), Measurable.piecewise hTm measurable_const hf.measurable_mk,
    fun x => ?_, ?_⟩
  · by_cases hx : x ∈ T
    · simp [hx]
    · have : f x = hf.mk f x := by
        by_contra h
        exact hx (subset_toMeasurable _ _ h)
      simp [hx, this]
  · have : ∀ᵐ x ∂μ, x ∉ T := by
      rw [ae_iff]; simpa using hT0
    filter_upwards [this, hf.ae_eq_mk] with x hx hx'
    simp [hx, hx']

end PDE.PrekopaLeindlerProof
