module

public import PDEFoundation.Measure.CappedENNReal
public import PDEFoundation.Measure.WeightedSuperlevelLayercake

/-! # Capped moments from localized distribution inequalities -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- A localized weak distribution inequality gives the exact integrated
inequality underlying the sharp dyadic maximal bound. No target moment is
assumed finite, and all quantities remain extended nonnegative integrals. -/
theorem capped_moment_le_weighted_moment_of_localized_distribution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ)
    (F : α → ℝ≥0∞) (hF : Measurable F) {q : ℝ} (hq : 1 < q)
    (hdist : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < F x} ≤
        ∫⁻ x in {x | ENNReal.ofReal t < F x}, ENNReal.ofReal |b x| ∂μ)
    (N : NNReal) :
    ENNReal.ofReal (q - 1) *
        (∫⁻ x, ENNReal.ofReal ((cappedENNReal (F x) N) ^ q) ∂μ) ≤
      ENNReal.ofReal q *
        ∫⁻ x, ENNReal.ofReal |b x| *
          ENNReal.ofReal ((cappedENNReal (F x) N) ^ (q - 1)) ∂μ := by
  let f : α → ℝ := fun x => cappedENNReal (F x) N
  have hf : Measurable f := PDE.Measurable.cappedENNReal hF N
  have hfnn (x : α) : 0 ≤ f x := cappedENNReal_nonneg _ _
  have hcap (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal t * μ {x | t < f x} ≤
        ∫⁻ x in {x | t < f x}, ENNReal.ofReal |b x| ∂μ := by
    by_cases htN : t < (N : ℝ)
    · have hset : {x | t < f x} = {x | ENNReal.ofReal t < F x} := by
        ext x
        exact (lt_cappedENNReal_iff ht.le).trans (and_iff_left htN)
      rw [hset]
      exact hdist t ht
    · have hset : {x | t < f x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (not_lt_of_ge ((cappedENNReal_le (F x) N).trans (le_of_not_gt htN))) hx
      simp only [hset, measure_empty, mul_zero, Measure.restrict_empty, lintegral_zero_measure]
      exact le_rfl
  have hkernel (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1)) ≤
        (∫⁻ x in {x | t < f x}, ENNReal.ofReal |b x| ∂μ) *
          ENNReal.ofReal (t ^ (q - 2)) := by
    have hp : t * t ^ (q - 2) = t ^ (q - 1) := by
      calc
        t * t ^ (q - 2) = t ^ (1 : ℝ) * t ^ (q - 2) := by rw [Real.rpow_one]
        _ = t ^ (1 + (q - 2)) := (Real.rpow_add (show 0 < t from ht) _ _).symm
        _ = t ^ (q - 1) := by congr 1; ring
    calc
      μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1)) =
          (ENNReal.ofReal t * μ {x | t < f x}) *
            ENNReal.ofReal (t ^ (q - 2)) := by
        rw [← hp, ENNReal.ofReal_mul (show 0 ≤ t from le_of_lt ht)]
        ac_rfl
      _ ≤ _ := mul_le_mul_left (hcap t ht) _
  have hint := setLIntegral_mono' (μ := volume) measurableSet_Ioi hkernel
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ hfnn) hf.aemeasurable (zero_lt_one.trans hq)
  have hweighted := weighted_superlevel_layercake μ b hb f hf.aemeasurable hfnn hq
  rw [hlayer, ← hweighted]
  calc
    ENNReal.ofReal (q - 1) *
        (ENNReal.ofReal q *
          ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal (t ^ (q - 1))) ≤
      ENNReal.ofReal (q - 1) *
        (ENNReal.ofReal q *
          ∫⁻ t in Ioi (0 : ℝ),
            (∫⁻ x in {x | t < f x}, ENNReal.ofReal |b x| ∂μ) *
              ENNReal.ofReal (t ^ (q - 2))) :=
      mul_le_mul_right (mul_le_mul_right hint _) _
    _ = _ := by ac_rfl

end PDE
