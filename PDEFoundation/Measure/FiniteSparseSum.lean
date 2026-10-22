module

public import PDEFoundation.Geometry.DyadicBox
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Literal finite sums on dyadic boxes -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A literal finite sum of constants supported on dyadic descendants. -/
def finiteSparseSum (I : Box (Fin d)) (S : Finset (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ) (x : Vec d) : ℝ :=
  ∑ p ∈ S, (dyadicDescendant I p : Set (Vec d)).indicator (fun _ => a p) x

/-- A finite sparse sum is measurable. -/
theorem measurable_finiteSparseSum (I : Box (Fin d))
    (S : Finset (List (Set (Fin d)))) (a : List (Set (Fin d)) → ℝ) :
    Measurable (finiteSparseSum I S a) := by
  unfold finiteSparseSum
  apply Finset.measurable_sum
  intro p hp
  exact measurable_const.indicator (measurableSet_dyadicDescendant I p)

/-- Nonnegative coefficients give a pointwise nonnegative sparse sum. -/
theorem finiteSparseSum_nonneg (I : Box (Fin d))
    (S : Finset (List (Set (Fin d)))) (a : List (Set (Fin d)) → ℝ)
    (ha : ∀ p ∈ S, 0 ≤ a p) (x : Vec d) :
    0 ≤ finiteSparseSum I S a x := by
  unfold finiteSparseSum
  exact Finset.sum_nonneg fun p hp =>
    Set.indicator_nonneg (fun _ _ => ha p hp) x

/-- Every finite sparse sum belongs to every finite positive `Lᵖ` space on
the root box. -/
theorem memLp_finiteSparseSum (I : Box (Fin d))
    (S : Finset (List (Set (Fin d)))) (a : List (Set (Fin d)) → ℝ)
    {p : ℝ} (_hp : 0 < p) :
    MemLp (finiteSparseSum I S a) (ENNReal.ofReal p)
      (volume.restrict (I : Set (Vec d))) := by
  unfold finiteSparseSum
  apply memLp_finsetSum
  intro q hq
  apply memLp_indicator_const
  · exact measurableSet_dyadicDescendant I q
  · right
    rw [Measure.restrict_apply (measurableSet_dyadicDescendant I q)]
    exact ((measure_mono Set.inter_subset_left).trans_lt
      (volume_dyadicDescendant_lt_top I q)).ne

/-- Exact pairing expansion for a nonnegative finite sparse sum and a
nonnegative measurable test function. -/
theorem lintegral_finiteSparseSum_mul_of_nonneg
    (I : Box (Fin d)) (S : Finset (List (Set (Fin d))))
    (a : List (Set (Fin d)) → ℝ) (φ : Vec d → ℝ)
    (ha : ∀ p ∈ S, 0 ≤ a p) (hφ : Measurable φ)
    (_hφ0 : ∀ x, 0 ≤ φ x) :
    (∫⁻ x in (I : Set (Vec d)),
      ENNReal.ofReal (finiteSparseSum I S a x) * ENNReal.ofReal (φ x)) =
      ∑ p ∈ S, ENNReal.ofReal (a p) *
        ∫⁻ x in (dyadicDescendant I p : Set (Vec d)), ENNReal.ofReal (φ x) := by
  have hpoint : (fun x =>
      ENNReal.ofReal (finiteSparseSum I S a x) * ENNReal.ofReal (φ x)) =
      fun x => ∑ p ∈ S,
        (dyadicDescendant I p : Set (Vec d)).indicator
          (fun y => ENNReal.ofReal (a p) * ENNReal.ofReal (φ y)) x := by
    funext x
    rw [finiteSparseSum, ENNReal.ofReal_sum_of_nonneg]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hxp : x ∈ (dyadicDescendant I p : Set (Vec d))
      · simp only [Set.indicator_of_mem hxp]
      · simp only [Set.indicator_of_notMem hxp, ENNReal.ofReal_zero, zero_mul]
    · intro p hp
      exact Set.indicator_nonneg (fun _ _ => ha p hp) x
  rw [hpoint, lintegral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro p hp
    change (∫⁻ x,
      (dyadicDescendant I p : Set (Vec d)).indicator
        (fun y => ENNReal.ofReal (a p) * ENNReal.ofReal (φ y)) x
        ∂volume.restrict (I : Set (Vec d))) = _
    rw [lintegral_indicator (measurableSet_dyadicDescendant I p)]
    rw [Measure.restrict_restrict (measurableSet_dyadicDescendant I p)]
    have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
      dyadicDescendant_le I p
    rw [Set.inter_eq_left.mpr hsub]
    rw [lintegral_const_mul]
    exact hφ.ennreal_ofReal
  · intro p hp
    exact ((hφ.ennreal_ofReal.const_mul _).indicator
      (measurableSet_dyadicDescendant I p))

end

end PDE
