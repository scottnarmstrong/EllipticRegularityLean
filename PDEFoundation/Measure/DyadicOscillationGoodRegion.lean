module

public import PDEFoundation.Measure.DyadicStoppingGeneration
public import PDEFoundation.Measure.DyadicBoxDifferentiation

/-! # Pointwise recovery off the first dyadic oscillation stops -/

@[expose] public section

namespace PDE

open BoxIntegral MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

variable {d m : ℕ}

/-- The union of literal first oscillation-stopping descendants is
measurable. -/
theorem measurableSet_iUnion_firstPrefixStop_dyadicOscillationBad
    (I : Box (Fin d)) (g : Vec d → Vec m) :
    MeasurableSet
      (⋃ q : List (Set (Fin d)),
        ⋃ (_ : IsFirstPrefixStop (dyadicOscillationBad I g) q),
          (dyadicDescendant I q : Set (Vec d))) := by
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_dyadicDescendant I q

/-- Away from the literal first stopping descendants, the pointwise field is
controlled by twice its root mean oscillation, almost everywhere. -/
theorem ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_of_not_mem_firstStops
    (I : Box (Fin d)) (hd : 0 < d) {g : Vec d → Vec m}
    (hg : ∀ i : Fin m,
      MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      x ∉ (⋃ q : List (Set (Fin d)),
        ⋃ (_ : IsFirstPrefixStop (dyadicOscillationBad I g) q),
          (dyadicDescendant I q : Set (Vec d))) →
      vecEuclideanNorm
          (g x - coordinateVectorAverage (I : Set (Vec d)) g) ≤
        2 * Real.sqrt (integralAverage (I : Set (Vec d))
          (fun y => vecNormSq
            (g y - coordinateVectorAverage (I : Set (Vec d)) g))) := by
  let c := coordinateVectorAverage (I : Set (Vec d)) g
  let h : Vec d → ℝ := fun y => vecNormSq (g y - c)
  let E : ℝ := integralAverage (I : Set (Vec d)) h
  have hItop : volume (I : Set (Vec d)) < ∞ := I.measure_coe_lt_top volume
  have hInt : IntegrableOn h (I : Set (Vec d)) volume :=
    integrableOn_vecNormSq_sub_const_of_coordinate_memLp hg hItop c
  have hDiff := ae_tendsto_integralAverage_dyadicBoxAtDepth I hd hInt
  filter_upwards [hDiff, ae_restrict_mem I.measurableSet_coe] with x hxDiff hxI
  intro hxGood
  have hmeans : ∀ n : ℕ,
      integralAverage (dyadicBoxAtDepth I x hxI n : Set (Vec d)) h ≤ 4 * E := by
    intro n
    have hnotBad :
        ¬dyadicOscillationBad I g (dyadicPathAtDepth I x hxI n) := by
      intro hbad
      obtain ⟨q, hqp, hqStop⟩ := exists_firstPrefixStop
        (dyadicOscillationBad I g) hbad
      apply hxGood
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqStop,
        dyadicDescendant_subset_of_isPrefix I hqp
          (mem_dyadicBoxAtDepth I x hxI n)⟩⟩
    apply le_of_not_gt
    intro hgt
    apply hnotBad
    exact hgt
  have hxSq : h x ≤ 4 * E := le_of_tendsto' (hxDiff hxI) hmeans
  have hEnonneg : 0 ≤ E := by
    exact integralAverage_nonneg I.measurableSet_coe
      (fun y _ => vecNormSq_nonneg (g y - c))
  have hsqrtSq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hEnonneg
  have hnormSq :
      (vecEuclideanNorm (g x - c)) ^ 2 = h x := vecEuclideanNorm_sq _
  dsimp only [c] at hnormSq ⊢
  nlinarith [Real.sqrt_nonneg E, vecEuclideanNorm_nonneg (g x -
    coordinateVectorAverage (I : Set (Vec d)) g)]

end

end PDE
