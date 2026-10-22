module

public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative superlevel bounds

This module contains the measure-theoretic level-set estimate used in the
De Giorgi recursion.  It is stated for an arbitrary measure and a restricted
set, so geometry enters only in later applications.

The hypotheses deliberately include integrability of the displayed power and
null measurability of the superlevel set for the restricted measure.  In
particular, the conclusion records that the superlevel measure is finite;
this is not hidden by the use of `ENNReal.toReal`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory Set

private theorem restrict_measure_superlevel_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {S : Set α} {k ell q : ℝ}
    (hkell : k < ell) (hq : 0 < q)
    (hpow : Integrable (fun x => (max (f x - k) 0) ^ q) (μ.restrict S)) :
    (μ.restrict S) {x | ell < f x} ≤
      ENNReal.ofReal
        ((∫ x in S, (max (f x - k) 0) ^ q ∂μ) / (ell - k) ^ q) := by
  let δ : ℝ := ell - k
  let g : α → ℝ := fun x => max (f x - k) 0
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hδq : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
  have hquot : Integrable (fun x => g x ^ q / δ ^ q) (μ.restrict S) := by
    exact hpow.div_const _
  have hquot_nonneg : 0 ≤ᵐ[μ.restrict S] fun x => g x ^ q / δ ^ q :=
    Filter.Eventually.of_forall fun x =>
      div_nonneg (Real.rpow_nonneg (le_max_right _ _) _) hδq.le
  calc
    (μ.restrict S) {x | ell < f x} ≤
        ENNReal.ofReal (∫ x, g x ^ q / δ ^ q ∂(μ.restrict S)) := by
      apply hquot.measure_le_integral hquot_nonneg
      intro x hx
      change ell < f x at hx
      have hδg : δ ≤ g x := by
        dsimp only [δ, g]
        have : ell - k < f x - k := by linarith
        exact this.le.trans (le_max_left _ _)
      have hpower : δ ^ q ≤ g x ^ q :=
        Real.rpow_le_rpow hδ.le hδg hq.le
      exact (le_div_iff₀ hδq).2 (by simpa only [one_mul] using hpower)
    _ = ENNReal.ofReal
        ((∫ x in S, (max (f x - k) 0) ^ q ∂μ) / (ell - k) ^ q) := by
      rw [integral_div]

/-- The strict superlevel of a positive-part truncation has finite restricted
measure when its displayed positive power is integrable. -/
theorem measure_inter_superlevel_lt_top
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {S : Set α} {k ell q : ℝ}
    (hkell : k < ell) (hq : 0 < q)
    (hlevel : NullMeasurableSet {x | ell < f x} (μ.restrict S))
    (hpow : Integrable (fun x => (max (f x - k) 0) ^ q) (μ.restrict S)) :
    μ (S ∩ {x | ell < f x}) < ⊤ := by
  have hbound := restrict_measure_superlevel_le hkell hq hpow
  have hfinite : (μ.restrict S) {x | ell < f x} < ⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  rw [Measure.restrict_apply₀ hlevel] at hfinite
  simpa only [inter_comm] using hfinite

/-- Quantitative positive-part superlevel estimate.  The measure is finite
under the displayed assumptions; see `measure_inter_superlevel_lt_top`. -/
theorem rpow_mul_measure_inter_superlevel_toReal_le_setIntegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {S : Set α} {k ell q : ℝ}
    (hkell : k < ell) (hq : 0 < q)
    (hlevel : NullMeasurableSet {x | ell < f x} (μ.restrict S))
    (hpow : Integrable (fun x => (max (f x - k) 0) ^ q) (μ.restrict S)) :
    (ell - k) ^ q * (μ (S ∩ {x | ell < f x})).toReal ≤
      ∫ x in S, (max (f x - k) 0) ^ q ∂μ := by
  let δ : ℝ := ell - k
  let g : α → ℝ := fun x => max (f x - k) 0
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hδq : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
  have hbound := restrict_measure_superlevel_le hkell hq hpow
  have hInt_nonneg : 0 ≤ ∫ x in S, g x ^ q ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (le_max_right _ _) _
  have hquot_nonneg : 0 ≤ (∫ x in S, g x ^ q ∂μ) / δ ^ q :=
    div_nonneg hInt_nonneg hδq.le
  have hreal :
      ((μ.restrict S) {x | ell < f x}).toReal ≤
        (∫ x in S, g x ^ q ∂μ) / δ ^ q := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [δ, g, ENNReal.toReal_ofReal hquot_nonneg] using h
  have hrestrict :
      (μ.restrict S) {x | ell < f x} = μ (S ∩ {x | ell < f x}) := by
    rw [Measure.restrict_apply₀ hlevel]
    simp only [inter_comm]
  have hlevel_real :
      (μ (S ∩ {x | ell < f x})).toReal ≤
        (∫ x in S, g x ^ q ∂μ) / δ ^ q := by
    simpa only [hrestrict] using hreal
  have hmul :
      (μ (S ∩ {x | ell < f x})).toReal * δ ^ q ≤
        ∫ x in S, g x ^ q ∂μ :=
    (le_div_iff₀ hδq).1 hlevel_real
  simpa only [δ, g, mul_comm] using hmul

/-- The squared superlevel estimate used with Caccioppoli energy in the
standard De Giorgi recursion. -/
theorem sq_mul_measure_inter_superlevel_toReal_le_setIntegral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {S : Set α} {k ell : ℝ}
    (hkell : k < ell)
    (hlevel : NullMeasurableSet {x | ell < f x} (μ.restrict S))
    (hpow : Integrable (fun x => (max (f x - k) 0) ^ 2) (μ.restrict S)) :
    (ell - k) ^ 2 * (μ (S ∩ {x | ell < f x})).toReal ≤
      ∫ x in S, (max (f x - k) 0) ^ 2 ∂μ := by
  simpa only [Real.rpow_two] using
    rpow_mul_measure_inter_superlevel_toReal_le_setIntegral
      (μ := μ) (q := (2 : ℝ)) hkell (by norm_num) hlevel
      (by simpa only [Real.rpow_two] using hpow)

/-- The critical-exponent form of the superlevel estimate used after the
zero-boundary Sobolev inequality in dimensions at least three. -/
theorem sq_mul_measure_inter_superlevel_rpow_le_setIntegral_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {d : ℕ} {f : α → ℝ} {S : Set α} {k ell : ℝ}
    (hd : 3 ≤ d) (hkell : k < ell)
    (hlevel : NullMeasurableSet {x | ell < f x} (μ.restrict S))
    (hpow : Integrable
      (fun x => (max (f x - k) 0) ^ (2 * (d : ℝ) / ((d : ℝ) - 2)))
      (μ.restrict S)) :
    (ell - k) ^ 2 * (μ (S ∩ {x | ell < f x})).toReal ^
        (((d : ℝ) - 2) / (d : ℝ)) ≤
      (∫ x in S, (max (f x - k) 0) ^ (2 * (d : ℝ) / ((d : ℝ) - 2)) ∂μ) ^
        (((d : ℝ) - 2) / (d : ℝ)) := by
  let p : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 2)
  let θ : ℝ := ((d : ℝ) - 2) / (d : ℝ)
  let δ : ℝ := ell - k
  let m : ℝ := (μ (S ∩ {x | ell < f x})).toReal
  let I : ℝ := ∫ x in S, (max (f x - k) 0) ^ p ∂μ
  have hd_real : 2 < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 2 < 3) hd
  have hd_pos : 0 < (d : ℝ) := lt_trans (by norm_num) hd_real
  have hd_sub_pos : 0 < (d : ℝ) - 2 := sub_pos.mpr hd_real
  have hp_pos : 0 < p := by
    dsimp only [p]
    positivity
  have hθ_nonneg : 0 ≤ θ := by
    dsimp only [θ]
    positivity
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hm : 0 ≤ m := by
    dsimp only [m]
    exact ENNReal.toReal_nonneg
  have hbase : δ ^ p * m ≤ I := by
    simpa only [p, δ, m, I] using
      rpow_mul_measure_inter_superlevel_toReal_le_setIntegral
        (μ := μ) hkell hp_pos hlevel hpow
  have hbase_nonneg : 0 ≤ δ ^ p * m := by
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) hm
  have hraised : (δ ^ p * m) ^ θ ≤ I ^ θ :=
    Real.rpow_le_rpow hbase_nonneg hbase hθ_nonneg
  have hexponent : p * θ = 2 := by
    dsimp only [p, θ]
    field_simp [hd_pos.ne', hd_sub_pos.ne']
  have hleft : (δ ^ p * m) ^ θ = δ ^ 2 * m ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hδ.le _) hm,
      ← Real.rpow_mul hδ.le, hexponent]
    simp only [Real.rpow_two]
  have hconclusion : δ ^ 2 * m ^ θ ≤ I ^ θ := by
    calc
    δ ^ 2 * m ^ θ = (δ ^ p * m) ^ θ := hleft.symm
    _ ≤ I ^ θ := hraised
  simpa only [δ, m, I, θ, p] using hconclusion

end PDE
