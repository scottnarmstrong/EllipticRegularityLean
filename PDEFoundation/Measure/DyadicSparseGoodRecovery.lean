module

public import PDEFoundation.Measure.DyadicOscillationGoodRegion
public import PDEFoundation.Measure.DyadicSparseRemainder

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory

/-- On one common full-measure subset of the root, the proved good-region
recovery estimate holds for every literal dyadic descendant. -/
theorem ae_good_recovery_all_dyadicDescendants
    {d m : ℕ} (I : Box (Fin d)) (hd : 0 < d) (g : Vec d → Vec m)
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn (I : Set (Vec d)))) :
    ∀ᵐ x ∂volume.restrict (I : Set (Vec d)),
      ∀ p : List (Set (Fin d)),
        x ∈ (dyadicDescendant I p : Set (Vec d)) →
        x ∉ dyadicOscillationStopUnion (dyadicDescendant I p) g →
        vecEuclideanNorm
            (g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) ≤
          2 * Real.sqrt (integralAverage (dyadicDescendant I p : Set (Vec d))
            (fun y => vecNormSq
              (g y - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g))) := by
  have hlocal (p : List (Set (Fin d))) : ∀ᵐ x ∂volume,
      x ∈ (dyadicDescendant I p : Set (Vec d)) →
      x ∉ dyadicOscillationStopUnion (dyadicDescendant I p) g →
      vecEuclideanNorm
          (g x - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g) ≤
        2 * Real.sqrt (integralAverage (dyadicDescendant I p : Set (Vec d))
          (fun y => vecNormSq
            (g y - coordinateVectorAverage (dyadicDescendant I p : Set (Vec d)) g))) := by
    have hgQ : ∀ i : Fin m, MemLp (fun x => g x i) 2
        (volumeOn (dyadicDescendant I p : Set (Vec d))) := fun i =>
      (hg i).mono_measure (Measure.restrict_mono (dyadicDescendant_le I p) le_rfl)
    exact (ae_restrict_iff' (measurableSet_dyadicDescendant I p)).mp
      (ae_vecEuclideanNorm_sub_coordinateVectorAverage_le_of_not_mem_firstStops
        (dyadicDescendant I p) hd hgQ)
  exact ae_restrict_of_ae (ae_all_iff.mpr hlocal)

end PDE
