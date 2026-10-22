module

public import PDEFoundation.Measure.NormalizedLp

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- A raw affine norm bound passes to one fixed volume normalization. The
constant contribution costs no further factor when the target mass is at
most the fixed normalizing volume. No target integrability is assumed. -/
theorem eLpNorm_fixedNormalization_le_of_raw_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    {V : ENNReal} (hV : V ≠ ∞) (hmass : μ Set.univ ≤ V)
    {p : ℝ} (hp : 0 < p) (A B : ENNReal)
    (hraw : eLpNorm f (ENNReal.ofReal p) μ ≤
      A * (μ Set.univ) ^ (1 / p) + B * eLpNorm g (ENNReal.ofReal p) ν) :
    eLpNorm f (ENNReal.ofReal p) (V⁻¹ • μ) ≤
      A + B * eLpNorm g (ENNReal.ofReal p) (V⁻¹ • ν) := by
  have hinv : V⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hV
  have hscale (δ : Measure α) :
      eLpNorm f (ENNReal.ofReal p) (V⁻¹ • δ) =
        V⁻¹ ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) δ := by
    rw [eLpNorm_smul_measure_of_ne_zero hinv]
    simp only [smul_eq_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  have hgscale : eLpNorm g (ENNReal.ofReal p) (V⁻¹ • ν) =
      V⁻¹ ^ (1 / p) * eLpNorm g (ENNReal.ofReal p) ν := by
    rw [eLpNorm_smul_measure_of_ne_zero hinv]
    simp only [smul_eq_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le]
  have hr : 0 ≤ 1 / p := (one_div_pos.mpr hp).le
  have hmass' : V⁻¹ * μ Set.univ ≤ 1 :=
    (mul_le_mul_right hmass _).trans (ENNReal.inv_mul_le_one V)
  have hfactor : V⁻¹ ^ (1 / p) * (μ Set.univ) ^ (1 / p) ≤ 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hr]
    exact ENNReal.rpow_le_one hmass' hr
  rw [hscale μ, hgscale]
  calc
    _ ≤ V⁻¹ ^ (1 / p) *
        (A * (μ Set.univ) ^ (1 / p) + B * eLpNorm g (ENNReal.ofReal p) ν) :=
      mul_le_mul_right hraw _
    _ = A * (V⁻¹ ^ (1 / p) * (μ Set.univ) ^ (1 / p)) +
        B * (V⁻¹ ^ (1 / p) * eLpNorm g (ENNReal.ofReal p) ν) := by ring
    _ ≤ A + B * (V⁻¹ ^ (1 / p) * eLpNorm g (ENNReal.ofReal p) ν) := by
      simpa only [mul_one] using add_le_add (mul_le_mul_right hfactor A) le_rfl

end PDE
