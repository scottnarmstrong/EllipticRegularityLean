module

public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Restricted-set Hölder estimates

This module records the finite-measure restriction estimate used in the
De Giorgi iteration.  It is deliberately measure-generic: geometry enters
only when a later module supplies the measure of a ball or cube.

The conclusion is written with real integrals and `Real.rpow`, rather than an
extended-real norm, because this is the form consumed by the level-set
recurrence.  The hypotheses retain both the finite-measure condition and the
restricted `L^q` membership needed for every displayed term to be finite.
No measurability assumption on the restricting set is needed: Mathlib's
restricted measure makes the statement meaningful for every set.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory Set

/-- On a finite restriction, an `L^q` function controls its `L^p` integral
for `0 < p < q`.  This is the exact restricted Hölder estimate with the
measure factor displayed explicitly. -/
theorem setIntegral_abs_rpow_le_setIntegral_abs_rpow_rpow_mul_measure_toReal_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : Set α} {f : α → ℝ} {p q : ℝ}
    (hp : 0 < p) (hpq : p < q)
    (hAfin : μ A < ∞)
    (hf : MemLp f (ENNReal.ofReal q) (μ.restrict A)) :
    (∫ x in A, |f x| ^ p ∂μ) ≤
      (∫ x in A, |f x| ^ q ∂μ) ^ (p / q) *
        (μ A).toReal ^ (1 - p / q) := by
  let ν : Measure α := μ.restrict A
  have hq : 0 < q := hp.trans hpq
  have hmeasure : ν Set.univ = μ A := by
    dsimp only [ν]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp only [univ_inter]
  have hpnorm : MemLp f (ENNReal.ofReal p) ν := by
    let : IsFiniteMeasure ν := ⟨by
      rw [hmeasure]
      exact hAfin⟩
    apply hf.mono_exponent
    exact ENNReal.ofReal_le_ofReal hpq.le
  have hExponent : 0 ≤ 1 / p - 1 / q := by
    rw [sub_nonneg, one_div, one_div]
    exact (inv_le_inv₀ hq hp).mpr hpq.le
  have hfactor_ne_top :
      (ν Set.univ) ^ (1 / (ENNReal.ofReal p).toReal -
        1 / (ENNReal.ofReal q).toReal) ≠ ∞ := by
    rw [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, hmeasure]
    exact ENNReal.rpow_ne_top_of_nonneg hExponent hAfin.ne
  have hright_ne_top :
      eLpNorm f (ENNReal.ofReal q) ν *
          (ν Set.univ) ^ (1 / (ENNReal.ofReal p).toReal -
            1 / (ENNReal.ofReal q).toReal) ≠ ∞ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hfactor_ne_top
  have hcompare :
      eLpNorm f (ENNReal.ofReal p) ν ≤
        eLpNorm f (ENNReal.ofReal q) ν *
          (ν Set.univ) ^ (1 / (ENNReal.ofReal p).toReal -
            1 / (ENNReal.ofReal q).toReal) := by
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := ν) (ENNReal.ofReal_le_ofReal hpq.le) hf.aestronglyMeasurable
  have hnorm :
      (eLpNorm f (ENNReal.ofReal p) ν).toReal ≤
        (eLpNorm f (ENNReal.ofReal q) ν).toReal *
          (μ A).toReal ^ (1 / p - 1 / q) := by
    have := ENNReal.toReal_mono hright_ne_top hcompare
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, hmeasure] using this
  have hnorm_rpow :
      (eLpNorm f (ENNReal.ofReal p) ν).toReal ^ p ≤
        ((eLpNorm f (ENNReal.ofReal q) ν).toReal *
          (μ A).toReal ^ (1 / p - 1 / q)) ^ p :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hnorm hp.le
  have hvalue_p :
      (eLpNorm f (ENNReal.ofReal p) ν).toReal ^ p =
        ∫ x in A, |f x| ^ p ∂μ := by
    simpa only [ν, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hpnorm
  have hvalue_q :
      (eLpNorm f (ENNReal.ofReal q) ν).toReal ^ q =
        ∫ x in A, |f x| ^ q ∂μ := by
    simpa only [ν, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hq hf
  have hnorm_q_nonneg : 0 ≤ (eLpNorm f (ENNReal.ofReal q) ν).toReal :=
    ENNReal.toReal_nonneg
  have hmeasure_nonneg : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hq_ne : q ≠ 0 := hq.ne'
  have hright :
      ((eLpNorm f (ENNReal.ofReal q) ν).toReal *
          (μ A).toReal ^ (1 / p - 1 / q)) ^ p =
        (∫ x in A, |f x| ^ q ∂μ) ^ (p / q) *
          (μ A).toReal ^ (1 - p / q) := by
    rw [Real.mul_rpow hnorm_q_nonneg
      (Real.rpow_nonneg hmeasure_nonneg _)]
    have hnorm_power :
        (eLpNorm f (ENNReal.ofReal q) ν).toReal ^ p =
          ((eLpNorm f (ENNReal.ofReal q) ν).toReal ^ q) ^ (p / q) := by
      rw [← Real.rpow_mul hnorm_q_nonneg]
      congr 1
      field_simp [hq_ne]
    have hmeasure_power :
        ((μ A).toReal ^ (1 / p - 1 / q)) ^ p =
          (μ A).toReal ^ (1 - p / q) := by
      rw [← Real.rpow_mul hmeasure_nonneg]
      congr 1
      field_simp [hp.ne', hq_ne]
    rw [hnorm_power, hvalue_q, hmeasure_power]
  calc
    (∫ x in A, |f x| ^ p ∂μ) =
        (eLpNorm f (ENNReal.ofReal p) ν).toReal ^ p := hvalue_p.symm
    _ ≤ ((eLpNorm f (ENNReal.ofReal q) ν).toReal *
          (μ A).toReal ^ (1 / p - 1 / q)) ^ p := hnorm_rpow
    _ = (∫ x in A, |f x| ^ q ∂μ) ^ (p / q) *
          (μ A).toReal ^ (1 - p / q) := hright

/-- The restricted critical-exponent estimate used in the `d ≥ 3` De Giorgi
recurrence.  The measure factor has exponent `2 / d`; equivalently, both
right-hand exponents are `(d - 2) / d` before multiplication by the outer
square. -/
theorem setIntegral_abs_rpow_two_le_setIntegral_abs_rpow_two_mul_div_sub_two_rpow_sub_div_mul_measure_toReal_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {A : Set α} {f : α → ℝ}
    (hd : 3 ≤ d) (hAfin : μ A < ∞)
    (hf : MemLp f (ENNReal.ofReal ((2 : ℝ) * d / ((d : ℝ) - 2)))
      (μ.restrict A)) :
    (∫ x in A, |f x| ^ (2 : ℝ) ∂μ) ≤
      (∫ x in A, |f x| ^ ((2 : ℝ) * d / ((d : ℝ) - 2)) ∂μ) ^
          (((d : ℝ) - 2) / (d : ℝ)) *
        (μ A).toReal ^ (2 / (d : ℝ)) := by
  have hd_two : (2 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 2 < 3) hd
  have hd_pos : (0 : ℝ) < d := by linarith
  have hd_sub_pos : (0 : ℝ) < (d : ℝ) - 2 := sub_pos.mpr hd_two
  have hcritical_gt_two :
      (2 : ℝ) < (2 : ℝ) * d / ((d : ℝ) - 2) := by
    rw [lt_div_iff₀ hd_sub_pos]
    linarith
  have hcritical_ratio :
      (2 : ℝ) / ((2 : ℝ) * d / ((d : ℝ) - 2)) =
        ((d : ℝ) - 2) / (d : ℝ) := by
    field_simp [hd_pos.ne', hd_sub_pos.ne']
  have hcritical_measure_ratio :
      1 - ((d : ℝ) - 2) / (d : ℝ) =
        2 / (d : ℝ) := by
    field_simp [hd_pos.ne']
    ring
  have h :=
    setIntegral_abs_rpow_le_setIntegral_abs_rpow_rpow_mul_measure_toReal_rpow
      (μ := μ) (A := A) (f := f) (p := (2 : ℝ))
      (q := (2 : ℝ) * d / ((d : ℝ) - 2))
      (by norm_num) hcritical_gt_two hAfin hf
  rw [hcritical_ratio, hcritical_measure_ratio] at h
  exact h

/-- The same critical restricted Hölder estimate with its quadratic left-hand
side written as `f²`.  No sign condition is required, since the square of a
real number agrees with the square of its absolute value. -/
theorem setIntegral_sq_le_setIntegral_abs_rpow_two_mul_div_sub_two_rpow_sub_div_mul_measure_toReal_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {A : Set α} {f : α → ℝ}
    (hd : 3 ≤ d) (hAfin : μ A < ∞)
    (hf : MemLp f (ENNReal.ofReal ((2 : ℝ) * d / ((d : ℝ) - 2)))
      (μ.restrict A)) :
    (∫ x in A, f x ^ 2 ∂μ) ≤
      (∫ x in A, |f x| ^ ((2 : ℝ) * d / ((d : ℝ) - 2)) ∂μ) ^
          (((d : ℝ) - 2) / (d : ℝ)) *
        (μ A).toReal ^ (2 / (d : ℝ)) := by
  simpa only [Real.rpow_two, sq_abs] using
    setIntegral_abs_rpow_two_le_setIntegral_abs_rpow_two_mul_div_sub_two_rpow_sub_div_mul_measure_toReal_rpow
      (μ := μ) hd hAfin hf

end PDE
