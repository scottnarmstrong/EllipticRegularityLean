module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Integrating over disjoint families inside a containing set -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal Function

/-- The sum of extended nonnegative integrals over a countable disjoint
measurable family is bounded by the integral over any set containing every
member of the family. -/
theorem tsum_setLIntegral_le_of_pairwiseDisjoint
    {α β : Type*} [MeasurableSpace α] [Countable β]
    (μ : Measure α) (E : β → Set α) (U : Set α) (f : α → ℝ≥0∞)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (Disjoint on E))
    (hsub : ∀ i, E i ⊆ U) :
    (∑' i, ∫⁻ x in E i, f x ∂μ) ≤ ∫⁻ x in U, f x ∂μ := by
  rw [← lintegral_iUnion hE hdisj]
  exact lintegral_mono_set (iUnion_subset hsub)

/-- Finite version of disjoint integral packing. -/
theorem sum_setLIntegral_le_of_pairwiseDisjoint
    {α β : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset β) (E : β → Set α) (U : Set α)
    (f : α → ℝ≥0∞)
    (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hdisj : (S : Set β).PairwiseDisjoint E)
    (hsub : ∀ i ∈ S, E i ⊆ U) :
    (∑ i ∈ S, ∫⁻ x in E i, f x ∂μ) ≤ ∫⁻ x in U, f x ∂μ := by
  rw [← lintegral_biUnion_finset hdisj hE]
  apply lintegral_mono_set
  intro x hx
  obtain ⟨i, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hi, hxi⟩ := mem_iUnion.mp hx
  exact hsub i hi hxi

end PDE
