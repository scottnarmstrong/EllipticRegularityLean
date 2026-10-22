module

public import PDEFoundation.Measure.VecAppendNormalizedLp
public import PDEFoundation.Measure.UniformNormalizedLp
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.VecAppendBall

/-! # Uniform lower norm comparison for a field extended in unused coordinates -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

/-- Native coordinate splitting gives the exact volume of a product cylinder. -/
theorem volume_preimage_vecAppendEquiv_prod
    (m n : ℕ) {U : Set (Vec m)} {V : Set (Vec n)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    volume (vecAppendEquiv m n ⁻¹' (U ×ˢ V)) = volume U * volume V := by
  have he := measurePreserving_vecAppendEquiv_restrict m n hU hV
  have h := he.measure_preimage
    (MeasurableSet.univ.nullMeasurableSet :
      NullMeasurableSet (Set.univ : Set (Vec m × Vec n))
        ((volume.restrict U).prod (volume.restrict V)))
  simpa only [preimage_univ, Measure.restrict_apply_univ,
    Measure.prod_apply, MeasurableSet.univ, lintegral_const,
    Measure.restrict_apply_univ, mul_comm] using h

/-- The normalized norm of the first-block profile on a half-radius ball is
bounded by the normalized norm of its coordinate lift on the full round ball.
The comparison constant depends only on the two dimensions and the radius,
and is chosen before the exponent or the profile. -/
theorem exists_uniform_lpMeanNormOn_comp_fst_le_on_euclideanBall
    (m n : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (p : ℝ), 2 ≤ p → ∀ (f : Vec m → ℝ),
      AEStronglyMeasurable f
        (volumeOn (euclideanBall (0 : Vec m) (R / 2))) →
      MemLp (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1)
        (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec (m + n)) R)) →
      (eLpNorm f (ENNReal.ofReal p)
        (normalizedVolumeOn (euclideanBall (0 : Vec m) (R / 2)))).toReal ≤
        K * (eLpNorm (fun z : Vec (m + n) => f (vecAppendEquiv m n z).1)
          (ENNReal.ofReal p)
          (normalizedVolumeOn (euclideanBall (0 : Vec (m + n)) R))).toReal := by
  let U := euclideanBall (0 : Vec m) (R / 2)
  let V := euclideanBall (0 : Vec n) (R / 2)
  let E := vecAppendEquiv m n ⁻¹' (U ×ˢ V)
  let W := euclideanBall (0 : Vec (m + n)) R
  have hhalf : 0 < R / 2 := half_pos hR
  have hU : MeasurableSet U := measurableSet_euclideanBall _ _
  have hV : MeasurableSet V := measurableSet_euclideanBall _ _
  have hUPos : 0 < volume U := volume_euclideanBall_pos _ hhalf
  have hVPos : 0 < volume V := volume_euclideanBall_pos _ hhalf
  have hUTop : volume U < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hhalf.le)
  have hVTop : volume V < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hhalf.le)
  have hEW : E ⊆ W :=
    preimage_vecAppendEquiv_prod_halfBall_subset_euclideanBall m n hR
  have hEPos : 0 < volume E := by
    rw [show volume E = volume U * volume V from
      volume_preimage_vecAppendEquiv_prod m n hU hV]
    exact ENNReal.mul_pos_iff.mpr ⟨hUPos, hVPos⟩
  have hWPos : 0 < volume W := volume_euclideanBall_pos _ hR
  have hWTop : volume W < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hR.le)
  have hETop : volume E < ⊤ := (measure_mono hEW).trans_lt hWTop
  obtain ⟨K, hK, hcomparison⟩ :=
    exists_uniform_lpMeanNormOn_le_of_volume_lower (E := ℝ)
      W hWPos hWTop (volume E) hEPos hETop
  refine ⟨K, hK, ?_⟩
  intro p hp f hfMeas hfLift
  obtain ⟨_hfE, hbound⟩ :=
    hcomparison p hp E hEW le_rfl
      (fun z => f (vecAppendEquiv m n z).1) hfLift
  have hnorm := eLpNorm_comp_fst_vecAppendEquiv_normalizedVolumeOn
    m n hU hV hUPos hUTop hVPos hVTop (p := ENNReal.ofReal p) hfMeas
  rw [hnorm] at hbound
  exact hbound

end PDE
