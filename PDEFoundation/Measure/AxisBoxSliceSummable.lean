module

public import PDEFoundation.Measure.AxisBoxSlice
public import PDEFoundation.Measure.CommonSquareRadius

/-!
# Vanishing errors on almost every axis-box slice

Dyadically summable planar `L²` errors have vanishing one-dimensional `L²`
errors on almost every vertical or horizontal slice.  The explicit `MemL2On`
hypotheses rule out any use of the convention that the Bochner integral of a
nonintegrable function is zero.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- Dyadically summable planar `L²` errors vanish in `L²` on almost every
vertical slice of an open planar axis box. -/
theorem ae_tendsto_axisBox_slice_second_sq_of_summable_dyadic
    {f : ℕ → Vec 2 → ℝ} {a b c d : ℝ}
    (hf : ∀ n, MemL2On (axisBox ![a, c] ![b, d]) (f n))
    (hsum : Summable fun n => (2 : ℝ) ^ n *
      ∫ x in axisBox ![a, c] ![b, d], (f n x) ^ 2) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      Tendsto
        (fun n => ∫ t in Icc c d, (f n (squarePoint s t)) ^ 2)
        atTop (nhds 0) := by
  let E : ℕ → ℝ → ℝ := fun n s =>
    (2 : ℝ) ^ n * ∫ t in Ioo c d, (f n (squarePoint s t)) ^ 2
  have hEIntegrable :
      ∀ n, IntegrableOn (E n) (Ioo a b) := by
    intro n
    exact
      (integrableOn_axisBox_innerIntegral_squarePoint
        (by simpa only [IntegrableOn] using (hf n).integrable_sq)).const_mul
        ((2 : ℝ) ^ n)
  have hEIntegral (n : ℕ) :
      (∫ s in Ioo a b, ‖E n s‖) =
        (2 : ℝ) ^ n *
          ∫ x in axisBox ![a, c] ![b, d], (f n x) ^ 2 := by
    have hEnonneg : ∀ s, 0 ≤ E n s := by
      intro s
      exact mul_nonneg (pow_nonneg (by norm_num) n)
        (integral_nonneg fun _ => sq_nonneg _)
    rw [show (fun s => ‖E n s‖) = E n by
      funext s
      rw [Real.norm_eq_abs, abs_of_nonneg (hEnonneg s)]]
    rw [show E n = fun s =>
        (2 : ℝ) ^ n * ∫ t in Ioo c d,
          (f n (squarePoint s t)) ^ 2 by rfl]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact
      (integralOn_axisBox_eq_integral_squarePoint
        (f := fun x => (f n x) ^ 2)
        (by simpa only [IntegrableOn] using (hf n).integrable_sq)).symm
  have hEIntegralSummable :
      Summable fun n => ∫ s in Ioo a b, ‖E n s‖ := by
    simpa only [hEIntegral] using hsum
  filter_upwards
      [ae_summable_of_summable_integral_norm hEIntegrable
        hEIntegralSummable] with s hs
  have hWeighted :
      Tendsto (fun n => E n s) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hNonneg : ∀ n, 0 ≤
      ∫ t in Icc c d, (f n (squarePoint s t)) ^ 2 := by
    intro n
    exact integral_nonneg fun _ => sq_nonneg _
  have hUpper : ∀ n,
      (∫ t in Icc c d, (f n (squarePoint s t)) ^ 2) ≤ E n s := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    dsimp only [E]
    calc
      (∫ t in Ioo c d, (f n (squarePoint s t)) ^ 2) =
          1 * ∫ t in Ioo c d, (f n (squarePoint s t)) ^ 2 :=
        (one_mul _).symm
      _ ≤ (2 : ℝ) ^ n *
          ∫ t in Ioo c d, (f n (squarePoint s t)) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          (integral_nonneg fun _ => sq_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hWeighted
    (Eventually.of_forall hNonneg) (Eventually.of_forall hUpper)

/-- Dyadically summable planar `L²` errors vanish in `L²` on almost every
horizontal slice of an open planar axis box. -/
theorem ae_tendsto_axisBox_slice_first_sq_of_summable_dyadic
    {f : ℕ → Vec 2 → ℝ} {a b c d : ℝ}
    (hf : ∀ n, MemL2On (axisBox ![a, c] ![b, d]) (f n))
    (hsum : Summable fun n => (2 : ℝ) ^ n *
      ∫ x in axisBox ![a, c] ![b, d], (f n x) ^ 2) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      Tendsto
        (fun n => ∫ s in Icc a b, (f n (squarePoint s t)) ^ 2)
        atTop (nhds 0) := by
  let E : ℕ → ℝ → ℝ := fun n t =>
    (2 : ℝ) ^ n * ∫ s in Ioo a b, (f n (squarePoint s t)) ^ 2
  have hEIntegrable :
      ∀ n, IntegrableOn (E n) (Ioo c d) := by
    intro n
    exact
      (integrableOn_axisBox_outerSecond_innerIntegral_squarePoint
        (by simpa only [IntegrableOn] using (hf n).integrable_sq)).const_mul
        ((2 : ℝ) ^ n)
  have hEIntegral (n : ℕ) :
      (∫ t in Ioo c d, ‖E n t‖) =
        (2 : ℝ) ^ n *
          ∫ x in axisBox ![a, c] ![b, d], (f n x) ^ 2 := by
    have hEnonneg : ∀ t, 0 ≤ E n t := by
      intro t
      exact mul_nonneg (pow_nonneg (by norm_num) n)
        (integral_nonneg fun _ => sq_nonneg _)
    rw [show (fun t => ‖E n t‖) = E n by
      funext t
      rw [Real.norm_eq_abs, abs_of_nonneg (hEnonneg t)]]
    rw [show E n = fun t =>
        (2 : ℝ) ^ n * ∫ s in Ioo a b,
          (f n (squarePoint s t)) ^ 2 by rfl]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact
      (integralOn_axisBox_eq_integral_outerSecond_squarePoint
        (f := fun x => (f n x) ^ 2)
        (by simpa only [IntegrableOn] using (hf n).integrable_sq)).symm
  have hEIntegralSummable :
      Summable fun n => ∫ t in Ioo c d, ‖E n t‖ := by
    simpa only [hEIntegral] using hsum
  filter_upwards
      [ae_summable_of_summable_integral_norm hEIntegrable
        hEIntegralSummable] with t ht
  have hWeighted :
      Tendsto (fun n => E n t) atTop (nhds 0) :=
    ht.tendsto_atTop_zero
  have hNonneg : ∀ n, 0 ≤
      ∫ s in Icc a b, (f n (squarePoint s t)) ^ 2 := by
    intro n
    exact integral_nonneg fun _ => sq_nonneg _
  have hUpper : ∀ n,
      (∫ s in Icc a b, (f n (squarePoint s t)) ^ 2) ≤ E n t := by
    intro n
    rw [integral_Icc_eq_integral_Ioo]
    dsimp only [E]
    calc
      (∫ s in Ioo a b, (f n (squarePoint s t)) ^ 2) =
          1 * ∫ s in Ioo a b, (f n (squarePoint s t)) ^ 2 :=
        (one_mul _).symm
      _ ≤ (2 : ℝ) ^ n *
          ∫ s in Ioo a b, (f n (squarePoint s t)) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          (integral_nonneg fun _ => sq_nonneg _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hWeighted
    (Eventually.of_forall hNonneg) (Eventually.of_forall hUpper)

end

end PDE
