module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Variational identity for weighted means

For a bounded measurable weight `0 ≤ ρ ≤ 1` and `g ∈ L²(μ)`, the weighted mean minimizes
`c ↦ ∫ (g - c)² ρ dμ`:
`∫ (g - a)² ρ = ∫ (g - c)² ρ + (c - a)² ∫ ρ` whenever `∫ (g - c) ρ = 0`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.Parabolic.WeakHarnack

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integrable_mul_weight {f ρ : α → ℝ} (hf : Integrable f μ) (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1) :
    Integrable (fun x => f x * ρ x) μ := by
  refine hf.norm.mono' (hf.1.mul hρm.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hρ0 x)]
  exact mul_le_of_le_one_right (norm_nonneg _) (hρ1 x)

theorem integrable_weight [IsFiniteMeasure μ] {ρ : α → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1) : Integrable ρ μ := by
  have := integrable_mul_weight (μ := μ) (integrable_const (1 : ℝ)) hρm hρ0 hρ1
  simpa using this

/-- Variational identity for the weighted mean. -/
theorem weighted_sq_sub_eq [IsFiniteMeasure μ] {g ρ : α → ℝ} (hg : MemLp g 2 μ) (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1) {c : ℝ} (a : ℝ)
    (hc : ∫ x, (g x - c) * ρ x ∂μ = 0) :
    ∫ x, (g x - a) ^ 2 * ρ x ∂μ =
      ∫ x, (g x - c) ^ 2 * ρ x ∂μ + (c - a) ^ 2 * ∫ x, ρ x ∂μ := by
  have h1 : Integrable (fun x => (g x - c) ^ 2 * ρ x) μ :=
    integrable_mul_weight (hg.sub (memLp_const c)).integrable_sq hρm hρ0 hρ1
  have h2 : Integrable (fun x => (g x - c) * ρ x) μ :=
    integrable_mul_weight (hg.integrable one_le_two |>.sub (integrable_const c)) hρm hρ0 hρ1
  have h3 : Integrable ρ μ := integrable_weight hρm hρ0 hρ1
  have : (fun x => (g x - a) ^ 2 * ρ x) =
      fun x => (g x - c) ^ 2 * ρ x + (2 * (c - a)) * ((g x - c) * ρ x) + (c - a) ^ 2 * ρ x := by
    funext x; ring
  have h4 : Integrable (fun x => 2 * (c - a) * ((g x - c) * ρ x)) μ := h2.const_mul _
  have h5 : Integrable (fun x => (c - a) ^ 2 * ρ x) μ := h3.const_mul _
  have h6 : Integrable (fun x => (g x - c) ^ 2 * ρ x + 2 * (c - a) * ((g x - c) * ρ x)) μ :=
    h1.add h4
  rw [this, integral_add h6 h5, integral_add h1 h4, integral_const_mul, integral_const_mul, hc]
  ring

end PDE.Parabolic.WeakHarnack
