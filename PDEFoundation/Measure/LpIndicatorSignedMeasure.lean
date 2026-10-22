module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-! # The signed measure induced by an `Lᵖ` functional on indicators -/

@[expose] public section

namespace PDE

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem sum_indicatorConstLp_eq_indicator_biUnion
    [IsFiniteMeasure μ] {p : ENNReal} (f : ℕ → Set α)
    (hf : ∀ n, MeasurableSet (f n))
    (hd : Pairwise (fun i j => Disjoint (f i) (f j))) (s : Finset ℕ) :
    ∑ n ∈ s, indicatorConstLp p (hf n) (measure_ne_top μ _) (1 : ℝ) =
      indicatorConstLp p (Finset.measurableSet_biUnion s (fun n _ => hf n))
        (measure_ne_top μ _)
        (1 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    have hdis : Disjoint (f n) (⋃ i ∈ s, f i) := by
      apply Set.disjoint_left.2
      intro x hxn hxunion
      obtain ⟨i, hxunion⟩ := Set.mem_iUnion.1 hxunion
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.1 hxunion
      exact Set.disjoint_left.1 (hd (by rintro rfl; exact hn hi)) hxn hxi
    rw [Finset.sum_insert hn, ih]
    calc
      _ = indicatorConstLp p ((hf n).union
            (Finset.measurableSet_biUnion s (fun i _ => hf i)))
          (measure_ne_top μ _) (1 : ℝ) :=
        (indicatorConstLp_disjoint_union (hf n)
          (Finset.measurableSet_biUnion s (fun i _ => hf i))
          (measure_ne_top μ _) (measure_ne_top μ _) hdis (1 : ℝ)).symm
      _ = _ := by
        congr 2
        ext x
        simp

private theorem hasSum_indicatorConstLp_of_pairwiseDisjoint
    [IsFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (f : ℕ → Set α) (hf : ∀ n, MeasurableSet (f n))
    (hd : Pairwise (fun i j => Disjoint (f i) (f j))) :
    HasSum
      (fun n => indicatorConstLp p (hf n) (measure_ne_top μ _) (1 : ℝ))
      (indicatorConstLp p (MeasurableSet.iUnion hf) (measure_ne_top μ _) (1 : ℝ)) := by
  classical
  let tail : ℕ → Set α := fun n => ⋃ i, ⋃ (_ : i ≥ n), f i
  have htailMeas : ∀ n, MeasurableSet (tail n) := fun n => by
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
  have htailMeasure : Tendsto (fun n => μ (tail n)) atTop (nhds 0) := by
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (Es := f) (fun i => (hf i).nullMeasurableSet) hd
  have htailIndicator : Tendsto
      (fun n => indicatorConstLp p (htailMeas n) (measure_ne_top μ _) (1 : ℝ))
      atTop (nhds 0) := by
    rw [← indicatorConstLp_empty (p := p) (μ := μ) (c := (1 : ℝ))]
    apply tendsto_indicatorConstLp_set hpTop
    simpa [tail, symmDiff_def] using htailMeasure
  have hsummable : Summable
      (fun n => indicatorConstLp p (hf n) (measure_ne_top μ _) (1 : ℝ)) := by
    apply summable_iff_vanishing_norm.2
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htailIndicator) ε hε
    refine ⟨Finset.range N, fun t hdis => ?_⟩
    rw [sum_indicatorConstLp_eq_indicator_biUnion f hf hd t]
    have hsub : (⋃ i ∈ t, f i) ⊆ tail N := by
      intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.1 hx
      apply Set.mem_iUnion.2
      refine ⟨i, Set.mem_iUnion.2 ⟨Nat.le_of_not_gt fun hiN => ?_, hxi⟩⟩
      exact (Finset.disjoint_left.1 hdis hi (Finset.mem_range.2 hiN)).elim
    have hnorm :
        ‖indicatorConstLp p
            (Finset.measurableSet_biUnion t (fun n _ => hf n)) (measure_ne_top μ _)
            (1 : ℝ)‖ ≤
          ‖indicatorConstLp p (htailMeas N) (measure_ne_top μ _) (1 : ℝ)‖ := by
      have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
      rw [norm_indicatorConstLp hp0 hpTop, norm_indicatorConstLp hp0 hpTop]
      simp only [norm_one, one_mul]
      apply Real.rpow_le_rpow
      · exact ENNReal.toReal_nonneg
      · exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
      · exact one_div_nonneg.mpr ENNReal.toReal_nonneg
    exact hnorm.trans_lt (by simpa only [dist_zero_right] using hN N le_rfl)
  apply hsummable.hasSum_iff_tendsto_nat.2
  rw [show (fun n => ∑ i ∈ Finset.range n,
      indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ)) =
      fun n => indicatorConstLp p
        (Finset.measurableSet_biUnion (Finset.range n) (fun i _ => hf i))
        (measure_ne_top μ _) (1 : ℝ) by
      funext n
      exact sum_indicatorConstLp_eq_indicator_biUnion f hf hd _]
  apply tendsto_indicatorConstLp_set hpTop
  have hsymm : (fun n : ℕ =>
      symmDiff (⋃ i ∈ Finset.range n, f i) (⋃ i, f i)) = tail := by
    funext n
    ext x
    simp only [mem_symmDiff, mem_iUnion, Finset.mem_range, tail]
    constructor
    · rintro (⟨⟨i, hi, hxi⟩, hall⟩ | ⟨⟨i, hxi⟩, hpartial⟩)
      · exact (hall ⟨i, hxi⟩).elim
      · refine ⟨i, le_of_not_gt fun hin => ?_, hxi⟩
        exact hpartial ⟨i, hin, hxi⟩
    · rintro ⟨i, hin, hxi⟩
      right
      refine ⟨⟨i, hxi⟩, ?_⟩
      rintro ⟨j, hjn, hxj⟩
      have hij : i ≠ j := by omega
      exact Set.disjoint_left.1 (hd hij) hxi hxj
  change Tendsto (fun n => μ ((fun n : ℕ =>
    symmDiff (⋃ i ∈ Finset.range n, f i) (⋃ i, f i)) n)) atTop (nhds 0)
  rw [hsymm]
  exact htailMeasure

open Classical in
/-- The standard signed measure obtained by evaluating an `Lᵖ` functional on
measurable-set indicators.  As required by Mathlib's `SignedMeasure` carrier,
its value on a nonmeasurable set is zero. -/
def lpIndicatorSignedMeasure [IsFiniteMeasure μ] (p : ENNReal)
    [Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (L : Lp ℝ p μ →L[ℝ] ℝ) : SignedMeasure α where
  measureOf' A := if hA : MeasurableSet A then
    L (indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ))
  else 0
  empty' := by simp
  not_measurable' := by
    intro A hA
    exact dite_eq_right hA
  m_iUnion' := by
    intro f hf hd
    have hsum := hasSum_indicatorConstLp_of_pairwiseDisjoint
      (μ := μ) (p := p) hpTop f hf hd
    have hLsum := L.hasSum hsum
    convert hLsum using 1 <;>
      simp only [dite_eq_left (MeasurableSet.iUnion hf), dite_eq_left (hf _)]

/-- Evaluation of the indicator signed measure on a measurable set is exactly
the original functional applied to that set's `Lᵖ` indicator. -/
theorem lpIndicatorSignedMeasure_apply
    [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)] (hpTop : p ≠ ∞)
    (L : Lp ℝ p μ →L[ℝ] ℝ)
    {A : Set α} (hA : MeasurableSet A) :
    lpIndicatorSignedMeasure p hpTop L A =
      L (indicatorConstLp p hA
        (measure_ne_top μ A) (1 : ℝ)) := by
  simp [lpIndicatorSignedMeasure, hA]

/-- The signed measure induced by an `Lᵖ` functional is absolutely continuous
with respect to the original finite measure. -/
theorem lpIndicatorSignedMeasure_absolutelyContinuous
    [IsFiniteMeasure μ] (p : ENNReal) [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (L : Lp ℝ p μ →L[ℝ] ℝ) :
    lpIndicatorSignedMeasure p hpTop L ≪ᵥ μ.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro A hA hμA
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hμA
  rw [lpIndicatorSignedMeasure_apply p hpTop L hA]
  have hind : indicatorConstLp p hA
      (measure_ne_top μ A) (1 : ℝ) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_indicatorConstLp hp0 hpTop]
    have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
    simp [measureReal_def, hμA, hpReal.ne']
  rw [hind, map_zero]

end

end PDE
