module

public import PDEFoundation.Sobolev.Cutoff.AxisBox
public import PDEFoundation.Sobolev.H1.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Explicit planar axis-box cutoff errors

This module records the pointwise cutoff errors needed by the square trace
argument.  The integral estimates will use the same literal closed inset, so
no almost-everywhere boundary convention is hidden in their statements.
-/

@[expose] public section

noncomputable section

namespace PDE

open Filter MeasureTheory Set

namespace QuantitativeSmoothCutoff

private abbrev planarAxisBoxCutoff
    (a b c d : ℝ) {δ : ℝ} (hδ : 0 < δ) :=
  axisBoxInteriorQuantitativeSmoothCutoff a b c d hδ

private theorem one_sub_planarAxisBoxCutoff_nonneg
    {a b c d δ : ℝ} (hδ : 0 < δ) (x : Vec 2) :
    0 ≤ 1 - planarAxisBoxCutoff a b c d hδ x :=
  sub_nonneg.mpr ((planarAxisBoxCutoff a b c d hδ).le_one x)

private theorem one_sub_planarAxisBoxCutoff_le_one
    {a b c d δ : ℝ} (hδ : 0 < δ) (x : Vec 2) :
    1 - planarAxisBoxCutoff a b c d hδ x ≤ 1 := by
  linarith [(planarAxisBoxCutoff a b c d hδ).nonneg x]

/-- Pointwise value error of the planar cutoff is no larger than the original
square. -/
theorem sq_sub_mul_axisBoxInteriorCutoff_le
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (f : Vec 2 → ℝ) (x : Vec 2) :
    (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2 ≤ f x ^ 2 := by
  let η := planarAxisBoxCutoff a b c d hδ
  have hnonneg : 0 ≤ 1 - η x :=
    one_sub_planarAxisBoxCutoff_nonneg hδ x
  have hle : 1 - η x ≤ 1 :=
    one_sub_planarAxisBoxCutoff_le_one hδ x
  have hsq : (1 - η x) ^ 2 ≤ 1 :=
    (sq_le_one_iff₀ hnonneg).2 hle
  change (f x - η x * f x) ^ 2 ≤ f x ^ 2
  calc
    (f x - η x * f x) ^ 2 = (1 - η x) ^ 2 * f x ^ 2 := by ring
    _ ≤ 1 * f x ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = f x ^ 2 := one_mul _

/-- The cutoff value error vanishes pointwise on its closed plateau. -/
theorem sq_sub_mul_axisBoxInteriorCutoff_eq_zero_of_mem_inset
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (f : Vec 2 → ℝ) {x : Vec 2}
    (hx : x ∈ axisBoxInteriorInset a b c d δ) :
    (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2 = 0 := by
  let η := planarAxisBoxCutoff a b c d hδ
  change (f x - η x * f x) ^ 2 = 0
  rw [η.eq_one_on_inner x hx]
  ring

/-- A coordinatewise plateau-gradient error is no larger than the original
coordinate square. -/
theorem sq_one_sub_mul_axisBoxInteriorCutoff_le
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (h : Vec 2 → ℝ) (x : Vec 2) :
    ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2 ≤ h x ^ 2 := by
  let η := planarAxisBoxCutoff a b c d hδ
  have hnonneg : 0 ≤ 1 - η x :=
    one_sub_planarAxisBoxCutoff_nonneg hδ x
  have hle : 1 - η x ≤ 1 :=
    one_sub_planarAxisBoxCutoff_le_one hδ x
  have hsq : (1 - η x) ^ 2 ≤ 1 :=
    (sq_le_one_iff₀ hnonneg).2 hle
  change ((1 - η x) * h x) ^ 2 ≤ h x ^ 2
  calc
    ((1 - η x) * h x) ^ 2 = (1 - η x) ^ 2 * h x ^ 2 := by ring
    _ ≤ 1 * h x ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = h x ^ 2 := one_mul _

/-- The plateau-gradient error vanishes pointwise on the closed inset. -/
theorem sq_one_sub_mul_axisBoxInteriorCutoff_eq_zero_of_mem_inset
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (h : Vec 2 → ℝ) {x : Vec 2}
    (hx : x ∈ axisBoxInteriorInset a b c d δ) :
    ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2 = 0 := by
  let η := planarAxisBoxCutoff a b c d hδ
  change ((1 - η x) * h x) ^ 2 = 0
  rw [η.eq_one_on_inner x hx]
  ring

/-- The multiplier term has the explicit coordinatewise `32 / δ` pointwise
bound. -/
theorem sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (f : Vec 2 → ℝ) (i : Fin 2) (x : Vec 2) :
    (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2 ≤
      (32 / δ) ^ 2 * f x ^ 2 := by
  let η := planarAxisBoxCutoff a b c d hδ
  have hgrad : |classicalGradient η.toFun x i| ≤ 32 / δ :=
    abs_classicalGradient_axisBoxInteriorCutoff_apply_le hδ x i
  change (f x * classicalGradient η.toFun x i) ^ 2 ≤
    (32 / δ) ^ 2 * f x ^ 2
  calc
    (f x * classicalGradient η.toFun x i) ^ 2 =
        |classicalGradient η.toFun x i| ^ 2 * f x ^ 2 := by
      rw [sq_abs]
      ring
    _ ≤ (32 / δ) ^ 2 * f x ^ 2 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hgrad 2) (sq_nonneg _)

/-- The multiplier term vanishes pointwise on the closed inset. -/
theorem sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_eq_zero_of_mem_inset
    {a b c d δ : ℝ} (hδ : 0 < δ)
    (f : Vec 2 → ℝ) (i : Fin 2) {x : Vec 2}
    (hx : x ∈ axisBoxInteriorInset a b c d δ) :
    (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2 = 0 := by
  let η := planarAxisBoxCutoff a b c d hδ
  change (f x * classicalGradient η.toFun x i) ^ 2 = 0
  rw [η.classicalGradient_eq_zero_of_mem_inner hx]
  simp

private theorem measurableSet_axisBoxInteriorInset
    (a b c d δ : ℝ) :
    MeasurableSet (axisBoxInteriorInset a b c d δ) := by
  unfold axisBoxInteriorInset
  exact (isClosed_set_pi fun i _ => by
    split_ifs <;> exact isClosed_Icc).measurableSet

private theorem integrableOn_sq_sub_mul_axisBoxInteriorCutoff
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    {f : Vec 2 → ℝ} (hf : MemL2On Q f) :
    IntegrableOn
      (fun x => (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2) Q := by
  have hmeas : AEStronglyMeasurable
      (fun x => f x - axisBoxInteriorCutoff a b c d δ x * f x)
      (volume.restrict Q) :=
    hf.aestronglyMeasurable.sub
      ((axisBoxInteriorCutoff_smooth a b c d δ).continuous.aestronglyMeasurable.mul
        hf.aestronglyMeasurable)
  have hfSq : IntegrableOn (fun x => f x ^ 2) Q := by
    simpa only [IntegrableOn] using hf.integrable_sq
  apply hfSq.mono' (hmeas.pow 2)
  filter_upwards with x
  change ‖(f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2‖ ≤ f x ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_sub_mul_axisBoxInteriorCutoff_le hδ f x

private theorem integrableOn_sq_one_sub_mul_axisBoxInteriorCutoff
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    {h : Vec 2 → ℝ} (hh : MemL2On Q h) :
    IntegrableOn
      (fun x => ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2) Q := by
  have hmeas : AEStronglyMeasurable
      (fun x => (1 - axisBoxInteriorCutoff a b c d δ x) * h x)
      (volume.restrict Q) := by
    have hcoeff : AEStronglyMeasurable
        (fun x : Vec 2 => 1 - axisBoxInteriorCutoff a b c d δ x)
        (volume.restrict Q) :=
      (continuous_const.sub
        (axisBoxInteriorCutoff_smooth a b c d δ).continuous).aestronglyMeasurable
    exact hcoeff.mul hh.aestronglyMeasurable
  have hhSq : IntegrableOn (fun x => h x ^ 2) Q := by
    simpa only [IntegrableOn] using hh.integrable_sq
  apply hhSq.mono' (hmeas.pow 2)
  filter_upwards with x
  change ‖((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2‖ ≤ h x ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_one_sub_mul_axisBoxInteriorCutoff_le hδ h x

private theorem integrableOn_sq_mul_classicalGradient_axisBoxInteriorCutoff_apply
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    {f : Vec 2 → ℝ} (i : Fin 2) (hf : MemL2On Q f) :
    IntegrableOn
      (fun x => (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2)
      Q := by
  have hcutoffOne : ContDiff ℝ 1 (axisBoxInteriorCutoff a b c d δ) :=
    (axisBoxInteriorCutoff_smooth a b c d δ).of_le (by simp)
  have hgradCont : Continuous
      (fun x => classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) :=
    continuous_apply i |>.comp
      (PDE.ContDiff.continuous_classicalGradient hcutoffOne)
  have hmeas : AEStronglyMeasurable
      (fun x => f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i)
      (volume.restrict Q) :=
    hf.aestronglyMeasurable.mul hgradCont.aestronglyMeasurable
  have hfSq : IntegrableOn (fun x => f x ^ 2) Q := by
    simpa only [IntegrableOn] using hf.integrable_sq
  apply (hfSq.const_mul ((32 / δ) ^ 2)).mono' (hmeas.pow 2)
  filter_upwards with x
  change ‖(f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2‖ ≤
    (32 / δ) ^ 2 * f x ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le hδ f i x

/-- The squared value error of the planar cutoff is carried by the complement
of its closed inset. -/
theorem setIntegral_sq_sub_mul_axisBoxInteriorCutoff_le
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    (hQ : MeasurableSet Q) {f : Vec 2 → ℝ} (hf : MemL2On Q f) :
    ∫ x in Q, (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2 ∂volume ≤
      ∫ x in Q \ axisBoxInteriorInset a b c d δ, f x ^ 2 ∂volume := by
  let J := Q \ axisBoxInteriorInset a b c d δ
  have hJ : MeasurableSet J :=
    hQ.diff (measurableSet_axisBoxInteriorInset a b c d δ)
  have hJQ : J ⊆ Q := sdiff_subset
  have hleft : IntegrableOn
      (fun x => (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2) Q :=
    integrableOn_sq_sub_mul_axisBoxInteriorCutoff
      (a := a) (b := b) (c := c) (d := d) hδ hf
  have hfSq : IntegrableOn (fun x => f x ^ 2) Q := by
    simpa only [IntegrableOn] using hf.integrable_sq
  have hright : IntegrableOn (J.indicator fun x => f x ^ 2) Q :=
    hfSq.indicator hJ
  calc
    ∫ x in Q, (f x - axisBoxInteriorCutoff a b c d δ x * f x) ^ 2 ∂volume ≤
        ∫ x in Q, J.indicator (fun x => f x ^ 2) x ∂volume := by
      apply setIntegral_mono_on hleft hright hQ
      intro x hxQ
      by_cases hx : x ∈ axisBoxInteriorInset a b c d δ
      · rw [sq_sub_mul_axisBoxInteriorCutoff_eq_zero_of_mem_inset hδ f hx]
        have hxJ : x ∉ J := by
          intro hxJ
          exact hxJ.2 hx
        rw [Set.indicator_of_notMem hxJ]
      · have hxJ : x ∈ J := ⟨hxQ, hx⟩
        rw [Set.indicator_of_mem hxJ]
        exact sq_sub_mul_axisBoxInteriorCutoff_le hδ f x
    _ = ∫ x in J, f x ^ 2 ∂volume := by
      rw [setIntegral_indicator hJ]
      rw [Set.inter_eq_right.mpr hJQ]
    _ = ∫ x in Q \ axisBoxInteriorInset a b c d δ, f x ^ 2 ∂volume := rfl

/-- The squared plateau-gradient error is carried by the complement of the
closed inset. -/
theorem setIntegral_sq_one_sub_mul_axisBoxInteriorCutoff_le
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    (hQ : MeasurableSet Q) {h : Vec 2 → ℝ} (hh : MemL2On Q h) :
    ∫ x in Q, ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2 ∂volume ≤
      ∫ x in Q \ axisBoxInteriorInset a b c d δ, h x ^ 2 ∂volume := by
  let J := Q \ axisBoxInteriorInset a b c d δ
  have hJ : MeasurableSet J :=
    hQ.diff (measurableSet_axisBoxInteriorInset a b c d δ)
  have hJQ : J ⊆ Q := sdiff_subset
  have hleft : IntegrableOn
      (fun x => ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2) Q :=
    integrableOn_sq_one_sub_mul_axisBoxInteriorCutoff
      (a := a) (b := b) (c := c) (d := d) hδ hh
  have hhSq : IntegrableOn (fun x => h x ^ 2) Q := by
    simpa only [IntegrableOn] using hh.integrable_sq
  have hright : IntegrableOn (J.indicator fun x => h x ^ 2) Q :=
    hhSq.indicator hJ
  calc
    ∫ x in Q, ((1 - axisBoxInteriorCutoff a b c d δ x) * h x) ^ 2 ∂volume ≤
        ∫ x in Q, J.indicator (fun x => h x ^ 2) x ∂volume := by
      apply setIntegral_mono_on hleft hright hQ
      intro x hxQ
      by_cases hx : x ∈ axisBoxInteriorInset a b c d δ
      · rw [sq_one_sub_mul_axisBoxInteriorCutoff_eq_zero_of_mem_inset hδ h hx]
        have hxJ : x ∉ J := by
          intro hxJ
          exact hxJ.2 hx
        rw [Set.indicator_of_notMem hxJ]
      · have hxJ : x ∈ J := ⟨hxQ, hx⟩
        rw [Set.indicator_of_mem hxJ]
        exact sq_one_sub_mul_axisBoxInteriorCutoff_le hδ h x
    _ = ∫ x in J, h x ^ 2 ∂volume := by
      rw [setIntegral_indicator hJ]
      rw [Set.inter_eq_right.mpr hJQ]
    _ = ∫ x in Q \ axisBoxInteriorInset a b c d δ, h x ^ 2 ∂volume := rfl

/-- The cutoff multiplier term is carried by the complement of the closed
inset, with the explicit coordinatewise constant `(32 / δ)²`. -/
theorem setIntegral_sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le
    {a b c d δ : ℝ} (hδ : 0 < δ) {Q : Set (Vec 2)}
    (hQ : MeasurableSet Q) {f : Vec 2 → ℝ} (i : Fin 2) (hf : MemL2On Q f) :
    ∫ x in Q,
        (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2 ∂volume ≤
      (32 / δ) ^ 2 *
        ∫ x in Q \ axisBoxInteriorInset a b c d δ, f x ^ 2 ∂volume := by
  let J := Q \ axisBoxInteriorInset a b c d δ
  have hJ : MeasurableSet J :=
    hQ.diff (measurableSet_axisBoxInteriorInset a b c d δ)
  have hJQ : J ⊆ Q := sdiff_subset
  have hleft : IntegrableOn
      (fun x => (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2)
      Q :=
    integrableOn_sq_mul_classicalGradient_axisBoxInteriorCutoff_apply
      (a := a) (b := b) (c := c) (d := d) hδ i hf
  have hfSq : IntegrableOn (fun x => f x ^ 2) Q := by
    simpa only [IntegrableOn] using hf.integrable_sq
  have hright : IntegrableOn (J.indicator fun x => (32 / δ) ^ 2 * f x ^ 2) Q :=
    (hfSq.const_mul ((32 / δ) ^ 2)).indicator hJ
  calc
    ∫ x in Q,
        (f x * classicalGradient (axisBoxInteriorCutoff a b c d δ) x i) ^ 2 ∂volume ≤
        ∫ x in Q, J.indicator (fun x => (32 / δ) ^ 2 * f x ^ 2) x ∂volume := by
      apply setIntegral_mono_on hleft hright hQ
      intro x hxQ
      by_cases hx : x ∈ axisBoxInteriorInset a b c d δ
      · rw [sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_eq_zero_of_mem_inset
          hδ f i hx]
        have hxJ : x ∉ J := by
          intro hxJ
          exact hxJ.2 hx
        rw [Set.indicator_of_notMem hxJ]
      · have hxJ : x ∈ J := ⟨hxQ, hx⟩
        rw [Set.indicator_of_mem hxJ]
        exact sq_mul_classicalGradient_axisBoxInteriorCutoff_apply_le hδ f i x
    _ = ∫ x in J, (32 / δ) ^ 2 * f x ^ 2 ∂volume := by
      rw [setIntegral_indicator hJ]
      rw [Set.inter_eq_right.mpr hJQ]
    _ = (32 / δ) ^ 2 * ∫ x in J, f x ^ 2 ∂volume := by
      rw [MeasureTheory.integral_const_mul]
    _ = (32 / δ) ^ 2 *
        ∫ x in Q \ axisBoxInteriorInset a b c d δ, f x ^ 2 ∂volume := rfl

end QuantitativeSmoothCutoff

end PDE
