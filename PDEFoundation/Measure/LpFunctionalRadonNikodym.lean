module

public import PDEFoundation.Measure.LpIndicatorSignedMeasure

/-! # Radon--Nikodym representation on measurable-set indicators -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A continuous functional on finite-measure real `Lᵖ`, for finite `p ≥ 1`,
has an integrable measurable Radon--Nikodym density that represents its values
on every measurable-set indicator. -/
theorem exists_integrable_rnDeriv_for_lpIndicator
    [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (L : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧
      ∀ (A : Set α) (hA : MeasurableSet A),
        L (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)) =
          ∫ x in A, g x ∂μ := by
  let s : SignedMeasure α := lpIndicatorSignedMeasure p hpTop L
  let g : α → ℝ := s.rnDeriv μ
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hac : s ≪ᵥ μ.toENNRealVectorMeasure :=
    lpIndicatorSignedMeasure_absolutelyContinuous p hp0 hpTop L
  have hdensity : μ.withDensityᵥ g = s :=
    SignedMeasure.withDensityᵥ_rnDeriv_eq s μ hac
  refine ⟨g, SignedMeasure.measurable_rnDeriv s μ,
    SignedMeasure.integrable_rnDeriv s μ, ?_⟩
  intro A hA
  rw [← lpIndicatorSignedMeasure_apply p hpTop L hA]
  change s A = ∫ x in A, g x ∂μ
  rw [← hdensity, withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv s μ) hA]

end

end PDE
