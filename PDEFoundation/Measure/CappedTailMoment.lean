module

public import PDEFoundation.Measure.CappedENNReal
public import PDEFoundation.Measure.WeightedTailLayercake

/-!
# Capped moments from high-tail distribution estimates

This generic lemma converts a weak distribution estimate with an integral
high tail into a strong finite-cap moment estimate.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- A high-tail distribution estimate implies the exact strong moment bound
for every finite real cap of an extended nonnegative function. -/
theorem lintegral_rpow_cappedENNReal_le_of_distribution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ)
    (F : α → ℝ≥0∞) (hF : Measurable F)
    {q C : ℝ} (hq : 1 < q) (hC : 0 ≤ C)
    (hdist : ∀ t : ℝ, 0 < t →
      μ {x | ENNReal.ofReal t < F x} ≤
        ENNReal.ofReal (C / t) *
          ∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ)
    (N : NNReal) :
    (∫⁻ x, ENNReal.ofReal ((cappedENNReal (F x) N) ^ q) ∂μ) ≤
      ENNReal.ofReal (C * q / (q - 1) * (2 : ℝ) ^ (q - 1)) *
        ∫⁻ x, ENNReal.ofReal (|b x| ^ q) ∂μ := by
  let f : α → ℝ := fun x => cappedENNReal (F x) N
  let T : ℝ≥0∞ :=
    ∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ) *
        ENNReal.ofReal (t ^ (q - 2))
  let B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|b x| ^ q) ∂μ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hqm1 : 0 < q - 1 := sub_pos.mpr hq
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all μ fun x => cappedENNReal_nonneg (F x) N)
    (PDE.Measurable.cappedENNReal hF N).aemeasurable hq0
  have hkernel (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal C *
          ((∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ) *
            ENNReal.ofReal (t ^ (q - 2))) := by
    have ht0 : 0 < t := ht
    have hsub : {x | t < f x} ⊆ {x | ENNReal.ofReal t < F x} := by
      intro x hx
      exact (lt_cappedENNReal_iff ht0.le).mp hx |>.1
    calc
      μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1)) ≤
          (ENNReal.ofReal (C / t) *
            ∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ) *
              ENNReal.ofReal (t ^ (q - 1)) :=
        mul_le_mul_left ((measure_mono hsub).trans (hdist t ht0)) _
      _ = ENNReal.ofReal C *
          ((∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ) *
            ENNReal.ofReal (t ^ (q - 2))) := by
        have hpow : 0 ≤ t ^ (q - 1) := Real.rpow_nonneg ht0.le _
        have hpow' : 0 ≤ t ^ (q - 2) := Real.rpow_nonneg ht0.le _
        have hreal : C / t * t ^ (q - 1) = C * t ^ (q - 2) := by
          have hp : t ^ (q - 2) = t ^ (q - 1) / t := by
            rw [show q - 2 = (q - 1) - 1 by ring,
              Real.rpow_sub_one ht0.ne']
          rw [hp]
          field_simp
        let tail : ℝ≥0∞ :=
          ∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| ∂μ
        change (ENNReal.ofReal (C / t) * tail) *
            ENNReal.ofReal (t ^ (q - 1)) =
          ENNReal.ofReal C * (tail * ENNReal.ofReal (t ^ (q - 2)))
        calc
          (ENNReal.ofReal (C / t) * tail) * ENNReal.ofReal (t ^ (q - 1)) =
              ENNReal.ofReal (C / t * t ^ (q - 1)) * tail := by
            rw [ENNReal.ofReal_mul (div_nonneg hC ht0.le)]
            ac_rfl
          _ = ENNReal.ofReal (C * t ^ (q - 2)) * tail := by rw [hreal]
          _ = ENNReal.ofReal C * (tail * ENNReal.ofReal (t ^ (q - 2))) := by
            rw [ENNReal.ofReal_mul hC]
            ac_rfl
  have hdistIntegral :
      (∫⁻ t in Ioi (0 : ℝ),
        μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1))) ≤
        ENNReal.ofReal C * T := by
    dsimp only [T]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Ioi hkernel
  have hweighted : ENNReal.ofReal (q - 1) * T =
      ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * B := by
    simpa only [T, B] using weighted_tail_layercake μ b hb hq
  have ha0 : ENNReal.ofReal (q - 1) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hqm1
  have haTop : ENNReal.ofReal (q - 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hT : T = (ENNReal.ofReal (q - 1))⁻¹ *
      (ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * B) := by
    calc
      T = (ENNReal.ofReal (q - 1))⁻¹ *
          (ENNReal.ofReal (q - 1) * T) := by
        rw [ENNReal.inv_mul_cancel_left ha0 haTop]
      _ = _ := by rw [hweighted]
  rw [show (∫⁻ x, ENNReal.ofReal (f x ^ q) ∂μ) =
      ENNReal.ofReal q *
        ∫⁻ t in Ioi (0 : ℝ),
          μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1)) from hlayer]
  calc
    ENNReal.ofReal q *
        (∫⁻ t in Ioi (0 : ℝ),
          μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1))) ≤
        ENNReal.ofReal q * (ENNReal.ofReal C * T) :=
      mul_le_mul_right hdistIntegral _
    _ = ENNReal.ofReal (C * q / (q - 1) * (2 : ℝ) ^ (q - 1)) * B := by
      rw [hT]
      rw [← ENNReal.ofReal_inv_of_pos hqm1]
      have hInv : 0 ≤ (q - 1)⁻¹ := inv_nonneg.mpr hqm1.le
      have hQC : 0 ≤ q * C := mul_nonneg hq0.le hC
      have hQCI : 0 ≤ q * C * (q - 1)⁻¹ := mul_nonneg hQC hInv
      have hcoeff :
          ENNReal.ofReal (q * C * (q - 1)⁻¹ * (2 : ℝ) ^ (q - 1)) =
            ENNReal.ofReal q * ENNReal.ofReal C * ENNReal.ofReal (q - 1)⁻¹ *
              ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) := by
        rw [ENNReal.ofReal_mul hQCI, ENNReal.ofReal_mul hQC,
          ENNReal.ofReal_mul hq0.le]
      calc
        ENNReal.ofReal q *
            (ENNReal.ofReal C *
              (ENNReal.ofReal (q - 1)⁻¹ *
                (ENNReal.ofReal ((2 : ℝ) ^ (q - 1)) * B))) =
            ENNReal.ofReal (q * C * (q - 1)⁻¹ * (2 : ℝ) ^ (q - 1)) * B := by
          rw [hcoeff]
          ac_rfl
        _ = ENNReal.ofReal (C * q / (q - 1) * (2 : ℝ) ^ (q - 1)) * B := by
          congr 2
          rw [div_eq_mul_inv]
          ring

end PDE
