module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Integrating high tails with their exact power factor -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- Weighted layer cake integrates the high-tail distribution with the exact
factor needed for the strong maximal estimate. All integrals are extended
nonnegative integrals; finiteness is not assumed. -/
theorem weighted_tail_layercake
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ) {q : ℝ} (hq : 1 < q) :
    ENNReal.ofReal (q - 1) *
      (∫⁻ t in Ioi (0 : ℝ),
        (∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ) *
          ENNReal.ofReal (t ^ (q - 2))) =
      ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) *
        ∫⁻ x, ENNReal.ofReal (|b x| ^ q) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal |b x|)
  have habs : AEMeasurable (fun x => |b x|) μ := by
    simpa only [Real.norm_eq_abs] using hb.norm.aemeasurable
  have hdensity : AEMeasurable (fun x => ENNReal.ofReal |b x|) μ := by
    simpa only [Real.enorm_eq_ofReal_abs] using hb.enorm
  have hdouble : AEMeasurable (fun x => 2 * |b x|) μ := habs.const_mul 2
  have hdoubleν : AEMeasurable (fun x => 2 * |b x|) ν :=
    hdouble.mono_ac (withDensity_absolutelyContinuous μ _)
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (ae_of_all _ (fun x => mul_nonneg (by norm_num) (abs_nonneg (b x))))
    hdoubleν (sub_pos.mpr hq)
  have hsets (t : ℝ) : {x | t < 2 * |b x|} = {x | t / 2 < |b x|} := by
    ext x
    constructor <;> intro hx <;> dsimp only [mem_ofPred_eq] at * <;> linarith
  have htail (t : ℝ) : ν {x | t < 2 * |b x|} =
      ∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ := by
    rw [hsets]
    exact withDensity_apply₀ _ (habs.nullMeasurableSet_preimage measurableSet_Ioi)
  simp_rw [htail, show q - 1 - 1 = q - 2 by ring] at hlayer
  rw [← hlayer]
  have hpowerMeas : AEMeasurable (fun x => ENNReal.ofReal ((2 * |b x|) ^ (q - 1))) μ :=
    (hdouble.pow_const _).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul₀ hdensity hpowerMeas]
  have hpoint (x : α) : ENNReal.ofReal |b x| *
      ENNReal.ofReal ((2 * |b x|) ^ (q - 1)) =
        ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * ENNReal.ofReal (|b x| ^ q) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    congr 1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)]
    have hp : |b x| * |b x| ^ (q - 1) = |b x| ^ q := by
      calc
        |b x| * |b x| ^ (q - 1) = |b x| ^ (1 : ℝ) * |b x| ^ (q - 1) := by
          rw [Real.rpow_one]
        _ = |b x| ^ (1 + (q - 1)) :=
          (Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (sub_nonneg.mpr hq.le)).symm
        _ = |b x| ^ q := by rw [add_sub_cancel]
    calc
      |b x| * (2 ^ (q - 1) * |b x| ^ (q - 1)) =
          2 ^ (q - 1) * (|b x| * |b x| ^ (q - 1)) := by ring
      _ = 2 ^ (q - 1) * |b x| ^ q := by rw [hp]
  simp_rw [Pi.mul_apply, hpoint]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end PDE
