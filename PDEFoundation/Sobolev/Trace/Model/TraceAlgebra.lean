module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Scalar and Jensen-type inequalities for the trace estimate

* a three-term convexity bound `(a + b + c)^p ≤ 2^{2(p-1)} (a^p + b^p + c^p)` in `[0, ∞]`;
* Jensen's inequality on `(0, 1]` in `lintegral` form.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set
open scoped ENNReal

/-- Three-term convexity. -/
theorem three_rpow_le {p : ℝ} (hp : 1 ≤ p) (a b c : ℝ≥0∞) :
    (a + b + c) ^ p ≤ (2 ^ (p - 1) * 2 ^ (p - 1)) * (a ^ p + b ^ p + c ^ p) := by
  have h2 : (1 : ℝ≥0∞) ≤ 2 ^ (p - 1) :=
    by
      have := ENNReal.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
        (show (0 : ℝ) ≤ p - 1 by linarith)
      simpa using this
  calc (a + b + c) ^ p ≤ 2 ^ (p - 1) * ((a + b) ^ p + c ^ p) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (a ^ p + b ^ p) + c ^ p) := by
        gcongr
        exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ 2 ^ (p - 1) * (2 ^ (p - 1) * (a ^ p + b ^ p + c ^ p)) := by
        gcongr
        calc 2 ^ (p - 1) * (a ^ p + b ^ p) + c ^ p
            ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) + 2 ^ (p - 1) * c ^ p := by
              gcongr
              exact le_mul_of_one_le_left zero_le h2
          _ = 2 ^ (p - 1) * (a ^ p + b ^ p + c ^ p) := by ring
    _ = _ := by ring

/-- Jensen on `(0, 1]`. -/
theorem lintegral_Ioc_unit_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫⁻ θ in Ioc (0 : ℝ) 1, f θ) ^ p ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, f θ ^ p := by
  rcases eq_or_lt_of_le hp with h1 | h1
  · subst h1; simp
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent h1
  have hp0 : 0 < p := by linarith
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) 1)) hpq hf
    (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ENNReal.one_rpow] at h
  calc (∫⁻ θ in Ioc (0 : ℝ) 1, f θ) ^ p
      ≤ ((∫⁻ θ in Ioc (0 : ℝ) 1, f θ ^ p) ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h hp0.le
    _ = _ := by
        rw [← ENNReal.rpow_mul]
        have : 1 / p * p = 1 := by field_simp
        rw [this, ENNReal.rpow_one]

end PDE.TraceLane
