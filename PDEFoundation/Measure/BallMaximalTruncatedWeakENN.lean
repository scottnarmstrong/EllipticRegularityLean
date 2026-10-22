module

public import PDEFoundation.Measure.BallMaximalTruncatedWeak

/-! # Extended integral form of the high-tail distribution estimate -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The absolute integral of an integrable tail is exactly the extended
integral over its literal superlevel set, allowing null measurable sets. -/
theorem ofReal_integral_abs_indicator_eq_setLIntegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b : α → ℝ) {A : Set α} (hA : NullMeasurableSet A μ)
    (hb : Integrable (A.indicator b) μ) :
    ENNReal.ofReal (∫ x, |A.indicator b x| ∂μ) =
      ∫⁻ x in A, ENNReal.ofReal |b x| ∂μ := by
  have hpoint : (fun x => ‖A.indicator b x‖ₑ) =
      A.indicator (fun x => ENNReal.ofReal |b x|) := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, enorm_zero]
  rw [show (fun x => |A.indicator b x|) = (fun x => ‖A.indicator b x‖) by
    funext x; exact (Real.norm_eq_abs _).symm,
    ofReal_integral_norm_eq_lintegral_enorm hb, hpoint, lintegral_indicator₀ hA]

/-- The genuine high-tail distribution estimate, expressed entirely with
extended nonnegative integrals for the layer-cake argument. -/
theorem volume_set_lt_uncenteredBallMaximal_le_tail_lintegral
    {d : ℕ} (b : Vec d → ℝ) {q : ℝ} (hq : 1 < q)
    (hb : MemLp b (ENNReal.ofReal q) volume) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < uncenteredBallMaximal b x} ≤
      ENNReal.ofReal ((2 * (3 : ℝ) ^ d) / t) *
        ∫⁻ x in {x | t / 2 < |b x|}, ENNReal.ofReal |b x| := by
  have habs : AEMeasurable (fun x => |b x|) volume := by
    simpa only [Real.norm_eq_abs] using hb.aestronglyMeasurable.norm.aemeasurable
  have hset : NullMeasurableSet {x | t / 2 < |b x|} volume :=
    habs.nullMeasurableSet_preimage measurableSet_Ioi
  have htail := integrable_indicator_abs_gt_of_memLp b (s := t / 2) hq
    (div_pos ht (by norm_num)) hb
  have h := volume_set_lt_uncenteredBallMaximal_le_tail b hq hb ht
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_abs_indicator_eq_setLIntegral b hset htail] at h
  exact h

end PDE
