module

public import PDEFoundation.Measure.DyadicSparseDomination
public import PDEFoundation.Measure.DyadicSparseForestSupport

/-! # Pointwise domination by a dyadic sparse forest -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Set Function
open scoped _root_.ENNReal

noncomputable section

variable {d m : ℕ} {ρ : Type*}

/-- A family of boxes with pairwise disjoint open interiors has a countable
index type. -/
theorem countable_of_pairwiseDisjoint_box_Ioo
    (root : ρ → Box (Fin d))
    (hroot : Pairwise fun i j => Disjoint (Box.Ioo (root i)) (Box.Ioo (root j))) :
    Countable ρ := by
  apply Pairwise.countable_of_isOpen_disjoint hroot
  · intro i
    exact isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo
  · intro i
    refine ⟨fun j => ((root i).lower j + (root i).upper j) / 2, ?_⟩
    intro j _hj
    constructor <;> linarith [(root i).lower_lt_upper j]

/-- On one ambient full-measure set, every root oscillation is dominated by
its literal sparse forest with the exact dimension coefficient. -/
theorem ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_dyadicSparseForest
    [Countable ρ]
    (root : ρ → Box (Fin d))
    (_hroot : Pairwise fun i j => Disjoint (Box.Ioo (root i)) (Box.Ioo (root j)))
    (hd : 0 < d) (g : ρ → Vec d → Vec m)
    (hg : ∀ i j, MemLp (fun x => g i x j) 2
      (volumeOn (root i : Set (Vec d)))) :
    ∀ᵐ x ∂volume, ∀ i,
      x ∈ (root i : Set (Vec d)) →
      ENNReal.ofReal (vecEuclideanNorm
          (g i x - coordinateVectorAverage (root i : Set (Vec d)) (g i))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
          ∑' j,
            dyadicSparseSum (root j) (dyadicSparseFamily (root j) (g j))
              (dyadicMeanOscillation (root j) (g j)) x := by
  have hlocal (i : ρ) : ∀ᵐ x ∂volume,
      x ∈ (root i : Set (Vec d)) →
      ENNReal.ofReal (vecEuclideanNorm
          (g i x - coordinateVectorAverage (root i : Set (Vec d)) (g i))) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2)) *
          dyadicSparseSum (root i) (dyadicSparseFamily (root i) (g i))
            (dyadicMeanOscillation (root i) (g i)) x :=
    (ae_restrict_iff' (root i).measurableSet_coe).mp
      (ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_dyadicSparseSum
        (root i) hd (g i) (hg i))
  apply ae_all_iff.mpr
  intro i
  filter_upwards [hlocal i] with x hx
  intro hxroot
  refine (hx hxroot).trans (mul_le_mul_right ?_ (ENNReal.ofReal ((2 : ℝ) ^ (1 + (d : ℝ) / 2))))
  exact ENNReal.le_tsum (f := fun j => dyadicSparseSum (root j) (dyadicSparseFamily (root j) (g j))
    (dyadicMeanOscillation (root j) (g j)) x) i

end

end PDE
