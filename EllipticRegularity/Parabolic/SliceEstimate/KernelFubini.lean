module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Prod


/-!
# Fubini for a bounded continuous kernel
-/

@[expose] public section

namespace PDE.Parabolic.Slice

open MeasureTheory Set

variable {d : ℕ}

/-- `∫ₓ f(x) ∫_y k(x-y) ψ(y) = ∫_y ψ(y) ∫ₓ f(x) k(x-y)` on a set of finite measure. -/
theorem kernel_fubini {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {μ : Measure E} [SFinite μ] {S : Set E}
    (hSfin : μ S < ⊤) {f ψ : E → ℝ}
    (hf : Integrable f (μ.restrict S)) (hψ : Integrable ψ (μ.restrict S)) {k : E → ℝ}
    (hk : Continuous fun p : E × E => k (p.1 - p.2)) (C : ℝ) (hkb : ∀ x, |k x| ≤ C) :
    ∫ x in S, f x * (∫ y in S, k (x - y) * ψ y ∂μ) ∂μ =
      ∫ y in S, ψ y * (∫ x in S, f x * k (x - y) ∂μ) ∂μ := by
  have : IsFiniteMeasure (μ.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
  set F : E → E → ℝ := fun x y => f x * k (x - y) * ψ y with hF
  have hint : Integrable (Function.uncurry F) ((μ.restrict S).prod (μ.restrict S)) := by
    have hb : Integrable (fun p : E × E => C * (|f p.1| * |ψ p.2|))
        ((μ.restrict S).prod (μ.restrict S)) :=
      (Integrable.mul_prod hf.norm hψ.norm).const_mul C
    refine Integrable.mono' hb ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : E × E => f p.1)
          ((μ.restrict S).prod (μ.restrict S)) :=
        hf.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst (μ := μ.restrict S) (ν := μ.restrict S))
      have h3 : AEStronglyMeasurable (fun p : E × E => ψ p.2)
          ((μ.restrict S).prod (μ.restrict S)) :=
        hψ.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := μ.restrict S) (ν := μ.restrict S))
      exact (h1.mul hk.aestronglyMeasurable).mul h3
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, hF, Real.norm_eq_abs, abs_mul]
      have := hkb (p.1 - p.2)
      have h0 : 0 ≤ |f p.1| := abs_nonneg _
      have h1 : 0 ≤ |ψ p.2| := abs_nonneg _
      nlinarith [mul_nonneg h0 h1, abs_nonneg (k (p.1 - p.2))]
  have := integral_integral_swap hint
  have e1 : ∀ x, ∫ y, F x y ∂(μ.restrict S) = f x * ∫ y in S, k (x - y) * ψ y ∂μ := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF]; ring
  have e2 : ∀ y, ∫ x, F x y ∂(μ.restrict S) = ψ y * ∫ x in S, f x * k (x - y) ∂μ := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]; ring
  simp only [e1, e2] at this
  exact this

end PDE.Parabolic.Slice
