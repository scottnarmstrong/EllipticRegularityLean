module

public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Passing to the limit `δ → 0` in the crossover product
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory Filter Topology

/-- The normalized `L¹` norm of a nonnegative function is the normalized lintegral. -/
theorem eLpMeanNormOn_one_eq {d : ℕ} {B : Set (Vec d)} (hBfin : volume B < ⊤) {f : Vec d → ℝ}
    (hfm : AEStronglyMeasurable f (volumeOn B)) (hf : ∀ᵐ x ∂(volumeOn B), 0 ≤ f x) :
    eLpMeanNormOn B 1 f = (volume B)⁻¹ * ∫⁻ x in B, ENNReal.ofReal (f x) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hBfin]
  simp only [eLpNormOn, ENNReal.toReal_one, div_one, ENNReal.rpow_one]
  rw [eLpNorm_one_eq_lintegral_enorm hfm]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hf] with x hx
  exact Real.enorm_eq_ofReal hx

/-- Monotone limit in the shift: given the bound for every shifted function, it holds for `u`. -/
theorem crossover_product_limit {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    (hu : AEMeasurable u μ) (hpos : ∀ᵐ x ∂μ, 0 < u x) {γ : ℝ} (hγ : 0 < γ)
    {R : ENNReal}
    (h : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal ((u x + 1 / ((n : ℝ) + 1)) ^ γ) ∂μ) *
        (∫⁻ x, ENNReal.ofReal ((u x + 1 / ((n : ℝ) + 1)) ^ (-γ)) ∂μ) ≤ R) :
    (∫⁻ x, ENNReal.ofReal (u x ^ γ) ∂μ) * (∫⁻ x, ENNReal.ofReal (u x ^ (-γ)) ∂μ) ≤ R := by
  set f : ℕ → α → ENNReal := fun n x => ENNReal.ofReal ((u x + 1 / ((n : ℝ) + 1)) ^ (-γ))
    with hf
  have hmeas : ∀ n, AEMeasurable (f n) μ := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hu.add_const _).pow_const _)
  have hmono : ∀ᵐ x ∂μ, ∀ n, f n x ≤ f (n + 1) x := by
    filter_upwards [hpos] with x hx n
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
    have : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith
    linarith
  have htend : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (ENNReal.ofReal (u x ^ (-γ)))) := by
    filter_upwards [hpos] with x hx
    refine (ENNReal.tendsto_ofReal ?_)
    have h0 : Tendsto (fun n : ℕ => u x + 1 / ((n : ℝ) + 1)) atTop (𝓝 (u x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h0
    exact h0.rpow_const (Or.inl hx.ne')
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeas
    (by filter_upwards [hmono] with x hx using monotone_nat_of_le_succ hx) htend
  by_cases hb : ∫⁻ x, ENNReal.ofReal (u x ^ (-γ)) ∂μ = 0
  · rw [hb, mul_zero]; exact zero_le
  have hlim2 := ENNReal.Tendsto.const_mul hlim
    (a := ∫⁻ x, ENNReal.ofReal (u x ^ γ) ∂μ) (Or.inl hb)
  refine le_of_tendsto' hlim2 fun n => ?_
  refine le_trans ?_ (h n)
  refine mul_le_mul' ?_ le_rfl
  refine lintegral_mono_ae ?_
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx.le ?_ hγ.le)
  have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

end PDE.DGNMLog
