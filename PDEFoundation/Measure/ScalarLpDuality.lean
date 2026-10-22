module

public import PDEFoundation.Measure.LpDensityTests
public import PDEFoundation.Measure.LpConjugateBoundFromTests
public import PDEFoundation.Measure.LpPairingEquality
public import PDEFoundation.Measure.LpPairingNorm
public import Mathlib.Basic.Real.ConjExponents

/-! # Genuine scalar `Lᵖ` dual representation on a finite measure space -/

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Every continuous functional on finite real `Lᑫ`, with `q = r/(r-1)`
and `r > 1`, is integration against an actual `Lʳ` element of exactly the same
norm. Radon--Nikodym, the conjugate membership, and representation on arbitrary
`Lᑫ` inputs are all derived internally. The `Fact` instances only equip the
standard quotient carriers with their normed space structures. -/
theorem exists_scalarLp_dual_density
    [IsFiniteMeasure μ] {r : ℝ} (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    [Fact (1 ≤ ENNReal.ofReal (r / (r - 1)))]
    (L : Lp ℝ (ENNReal.ofReal (r / (r - 1))) μ →L[ℝ] ℝ) :
    ∃ g : Lp ℝ (ENNReal.ofReal r) μ,
      (∀ f : Lp ℝ (ENNReal.ofReal (r / (r - 1))) μ,
        L f = ∫ x, g x * f x ∂μ) ∧ ‖g‖ = ‖L‖ := by
  have : ENNReal.HolderConjugate (ENNReal.ofReal r)
      (ENNReal.ofReal (r / (r - 1))) :=
    (Real.HolderConjugate.conjExponent hr).ennrealOfReal
  rcases exists_integrable_density_and_bounded_test_bound
      (ENNReal.ofReal (r / (r - 1))) ENNReal.ofReal_ne_top L with
    ⟨g, hgMeas, hgInt, hIndicator, hTest⟩
  rcases memLp_and_eLpNorm_le_of_bounded_conjugate_tests hr (norm_nonneg L)
      hgMeas hgInt hTest with ⟨hg, hNorm⟩
  have hEq := lpFunctional_eq_pairing_of_indicator_density
    ENNReal.ofReal_ne_top L hgInt hg hIndicator
  refine ⟨hg.toLp g, ?_, ?_⟩
  · intro f
    rw [hEq, ContinuousLinearMap.lpPairing_eq_integral]
    rfl
  · apply le_antisymm
    · simpa only [Lp.norm_toLp] using hNorm
    · rw [hEq]
      exact norm_scalarLpPairing_le _

end

end PDE
