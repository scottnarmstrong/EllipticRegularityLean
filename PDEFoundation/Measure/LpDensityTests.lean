module

public import PDEFoundation.Measure.LpFunctionalRadonNikodym
public import PDEFoundation.Measure.LpBoundedPairing

/-! # Genuine bounded-test estimates for an `Lᵖ` functional density -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An actual finite-exponent functional admits an integrable measurable
density whose pairing with every bounded test satisfies the operator norm
bound. The density is constructed internally by Radon--Nikodym. -/
theorem exists_integrable_density_and_bounded_test_bound
    [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)] (hpTop : p ≠ ⊤)
    (L : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧
      (∀ (A : Set α) (hA : MeasurableSet A),
        L (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ)) =
          ∫ x in A, g x ∂μ) ∧
      (∀ f : α → ℝ, Measurable f →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C) →
        |∫ x, f x * g x ∂μ| ≤ ‖L‖ * (eLpNorm f p μ).toReal) := by
  rcases exists_integrable_rnDeriv_for_lpIndicator p hpTop L with
    ⟨g, hgMeas, hgInt, hIndicator⟩
  refine ⟨g, hgMeas, hgInt, hIndicator, ?_⟩
  intro f hfMeas hfBound
  rcases hfBound with ⟨C, _, hC⟩
  rcases exists_memLp_and_apply_eq_integral_of_indicator_pairing hpTop
      L g hgInt hIndicator f hfMeas C (by simpa [Real.norm_eq_abs] using hC) with
    ⟨hf, hEq⟩
  rw [← hEq, ← Real.norm_eq_abs, ← Lp.norm_toLp f hf]
  exact L.le_opNorm _

end

end PDE
