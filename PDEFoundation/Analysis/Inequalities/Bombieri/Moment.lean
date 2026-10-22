module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The moment estimate in the Bombieri-Giusti lemma

Splitting at the level `exp lam` and applying Holder's inequality on the set where `f` is large.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

variable {X : Type*} [MeasurableSpace X]

/-- `‖f‖_α^α = ∫ |f|^α` for the real exponent `α > 0`. -/
theorem eLpNorm_rpow_eq_lintegral (μ : Measure X) {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {α : ℝ} (hα : 0 < α) :
    eLpNorm f (ENNReal.ofReal α) μ ^ α = ∫⁻ x, ‖f x‖ₑ ^ α ∂μ := by
  have hαne : ENNReal.ofReal α ≠ 0 := by simpa using hα
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hαne ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hα.le,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hα.ne', ENNReal.rpow_one]

/-- The Holder-type moment estimate of the Bombieri-Giusti one-step argument. -/
theorem moment_bound (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x) (T T1 : Set X)
    (_hT : MeasurableSet T) (hTT1 : T ⊆ T1) (c : ℝ) (hc : 0 ≤ c)
    (hlog : ∀ lam : ℝ, 0 < lam →
      ν (T1 ∩ {x | lam < Real.log (f x)}) ≤ ENNReal.ofReal (c / lam))
    (α₀ α lam N : ℝ) (hN0 : 0 ≤ N) (hα : 0 < α) (hαα₀ : 2 * α ≤ α₀) (hlam : 0 < lam) (hcl : c / lam ≤ 1)
    (hN : eLpNorm f (ENNReal.ofReal α₀) (ν.restrict T) = ENNReal.ofReal N) :
    eLpNorm f (ENNReal.ofReal α) (ν.restrict T) ^ α ≤
      ENNReal.ofReal (Real.exp (α * lam) + N ^ α * (c / lam) ^ (1 / 2 : ℝ)) := by
  have hα₀ : 0 < α₀ := by linarith
  set μ := ν.restrict T with hμ
  have hμ1 : μ Set.univ ≤ 1 := by
    rw [hμ, Measure.restrict_apply_univ]; exact prob_le_one
  set s : Set X := {x | Real.exp lam < f x} with hs
  have hsm : MeasurableSet s := measurableSet_lt measurable_const hf
  rw [eLpNorm_rpow_eq_lintegral μ hf.aestronglyMeasurable hα, ← lintegral_add_compl _ hsm]
  have hI1 : ∫⁻ x in sᶜ, ‖f x‖ₑ ^ α ∂μ ≤ ENNReal.ofReal (Real.exp (α * lam)) := by
    calc ∫⁻ x in sᶜ, ‖f x‖ₑ ^ α ∂μ
        ≤ ∫⁻ _ in sᶜ, ENNReal.ofReal (Real.exp (α * lam)) ∂μ := by
          refine setLIntegral_mono' hsm.compl ?_
          intro x hx
          have hx' : f x ≤ Real.exp lam := not_lt.mp hx
          rw [Real.enorm_eq_ofReal (hpos x).le,
            ENNReal.ofReal_rpow_of_nonneg (hpos x).le hα.le]
          apply ENNReal.ofReal_le_ofReal
          rw [mul_comm, Real.exp_mul]
          exact Real.rpow_le_rpow (hpos x).le hx' hα.le
      _ ≤ ENNReal.ofReal (Real.exp (α * lam)) := by
          rw [setLIntegral_const]
          calc _ ≤ ENNReal.ofReal (Real.exp (α * lam)) * 1 := by
                gcongr
                exact (measure_mono (Set.subset_univ _)).trans hμ1
            _ = _ := mul_one _
  have hI2 : ∫⁻ x in s, ‖f x‖ₑ ^ α ∂μ ≤ ENNReal.ofReal (N ^ α * (c / lam) ^ (1 / 2 : ℝ)) := by
    rw [← eLpNorm_rpow_eq_lintegral (μ.restrict s) hf.aestronglyMeasurable hα]
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
      (p := ENNReal.ofReal α) (q := ENNReal.ofReal α₀)
      (ENNReal.ofReal_le_ofReal (by linarith)) hf.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal hα.le, ENNReal.toReal_ofReal hα₀.le] at h2
    have hsmall : (μ.restrict s) Set.univ ≤ ENNReal.ofReal (c / lam) := by
      rw [Measure.restrict_apply_univ, hμ, Measure.restrict_apply hsm]
      refine le_trans (measure_mono ?_) (hlog lam hlam)
      intro x ⟨hxs, hxT⟩
      exact ⟨hTT1 hxT, (Real.lt_log_iff_exp_lt (hpos x)).mpr hxs⟩
    have hE : eLpNorm f (ENNReal.ofReal α₀) (μ.restrict s) ≤ ENNReal.ofReal N := by
      rw [← hN]; exact eLpNorm_mono_measure f Measure.restrict_le_self
    have hexp : 0 ≤ 1 / α - 1 / α₀ := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hα (by linarith)
    have h3 : eLpNorm f (ENNReal.ofReal α) (μ.restrict s) ≤
        ENNReal.ofReal N * ENNReal.ofReal (c / lam) ^ (1 / α - 1 / α₀) :=
      h2.trans (by gcongr)
    calc eLpNorm f (ENNReal.ofReal α) (μ.restrict s) ^ α
        ≤ (ENNReal.ofReal N * ENNReal.ofReal (c / lam) ^ (1 / α - 1 / α₀)) ^ α := by gcongr
      _ = ENNReal.ofReal N ^ α * ENNReal.ofReal (c / lam) ^ ((1 / α - 1 / α₀) * α) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le, ← ENNReal.rpow_mul]
      _ ≤ ENNReal.ofReal N ^ α * ENNReal.ofReal (c / lam) ^ (1 / 2 : ℝ) := by
          gcongr ENNReal.ofReal N ^ α * ?_
          refine ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr hcl) ?_
          have : (1 / α - 1 / α₀) * α = 1 - α / α₀ := by field_simp
          rw [this]
          have : α / α₀ ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hα₀ (by norm_num)]; linarith
          linarith
      _ = ENNReal.ofReal (N ^ α * (c / lam) ^ (1 / 2 : ℝ)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hN0 _),
            ENNReal.ofReal_rpow_of_nonneg hN0 hα.le,
            ENNReal.ofReal_rpow_of_nonneg (div_nonneg hc hlam.le) (by norm_num)]
  calc _ ≤ ENNReal.ofReal (N ^ α * (c / lam) ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal (Real.exp (α * lam)) := add_le_add hI2 hI1
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hN0 _)
        (Real.rpow_nonneg (div_nonneg hc hlam.le) _)) (Real.exp_pos _).le, add_comm]

end PDE.Bombieri
