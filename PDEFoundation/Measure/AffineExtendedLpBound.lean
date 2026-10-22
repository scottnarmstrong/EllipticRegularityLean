module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! # `Lᵖ` bounds from extended nonnegative affine majorants -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- A genuine almost-everywhere affine majorant by a measurable extended
nonnegative function gives the corresponding `Lᵖ` bound, without assuming
integrability or finiteness of the target. -/
theorem eLpNorm_le_of_ae_ofReal_abs_le_add_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (S : α → ENNReal) (hS : Measurable S)
    (hf : AEStronglyMeasurable f μ)
    {p A B : ℝ} (hp : 1 ≤ p) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ,
      ENNReal.ofReal |f x| ≤ ENNReal.ofReal A + ENNReal.ofReal B * S x) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal A * (μ Set.univ) ^ (1 / p) +
        ENNReal.ofReal B * eLpNorm S (ENNReal.ofReal p) μ := by
  let a : α → ENNReal := fun _ => ENNReal.ofReal A
  let g : α → ENNReal := fun x => ENNReal.ofReal B * S x
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpa : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hameas : Measurable a := measurable_const
  have hgmeas : Measurable g := measurable_const.mul hS
  have hmono : eLpNorm f (ENNReal.ofReal p) μ ≤
      eLpNorm (a + g) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_enorm_ae hf
    filter_upwards [hbound] with x hx
    simpa only [a, g, Pi.add_apply, enorm_eq_self,
      Real.enorm_eq_ofReal_abs (f x)] using hx
  have htriangle : eLpNorm (a + g) (ENNReal.ofReal p) μ ≤
      eLpNorm a (ENNReal.ofReal p) μ + eLpNorm g (ENNReal.ofReal p) μ :=
    eLpNorm_add_le hpa
  have haNorm : eLpNorm a (ENNReal.ofReal p) μ =
      ENNReal.ofReal A * (μ Set.univ) ^ (1 / p) := by
    rw [eLpNorm_const' (ENNReal.ofReal A)
      (by simp [ENNReal.ofReal_eq_zero, hp0.not_ge]) ENNReal.ofReal_ne_top]
    simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le]
  let c : NNReal := ⟨B, hB⟩
  have hc : (c : ENNReal) = ENNReal.ofReal B := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hgNorm : eLpNorm g (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal B * eLpNorm S (ENNReal.ofReal p) μ := by
    have hscale := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (μ := μ) (f := g) (g := S) (c := c) hgmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [g, enorm_eq_self, hc] using
          (le_refl (ENNReal.ofReal B * S x)))
      (ENNReal.ofReal p)
    simpa only [ENNReal.smul_def, smul_eq_mul, hc] using hscale
  exact hmono.trans (htriangle.trans (add_le_add haNorm.le hgNorm))

end PDE
