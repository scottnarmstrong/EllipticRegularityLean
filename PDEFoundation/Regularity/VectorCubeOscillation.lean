module

public import PDEFoundation.Regularity.CubeGradient
public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-!
# Coordinate cube oscillation of a vector field

This module compares the centered cube oscillation of one coordinate with the
native-vector centered mean `L²` seminorm.  It then enlarges the cube to its
standard enclosing Euclidean ball, retaining the exact volume-ratio constant.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- One coordinate of a vector field has no more centered mean-square
oscillation than the whole field measured with `vecNormSq`. -/
theorem sqrt_integralAverage_sq_sub_coordinate_mean_le_centeredVectorMeanL2
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUtop : volume U < ∞) (i : Fin d) :
    Real.sqrt (integralAverage U
        (fun x => (g x i - integralAverage U (fun y => g y i)) ^ 2)) ≤
      centeredVectorMeanL2 U g := by
  let m := vectorIntegralAverage U g
  have hcenter : MemVectorL2On U (fun x => g x - m) :=
    memVectorL2On_sub_const hg hUtop m
  have hcoordInt : IntegrableOn (fun x => ((g x - m) i) ^ 2) U := by
    simpa only [pow_two] using! (hcenter i).integrable_mul (hcenter i)
  have hvecInt : IntegrableOn (fun x => vecNormSq (g x - m)) U :=
    integrableOn_vecNormSq_of_memVectorL2On hcenter
  have hraw :
      (∫ x in U, ((g x - m) i) ^ 2) ≤
        ∫ x in U, vecNormSq (g x - m) :=
    integral_mono_ae hcoordInt hvecInt
      (Filter.Eventually.of_forall fun x => sq_apply_le_vecNormSq (g x - m) i)
  unfold centeredVectorMeanL2 integralAverage
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left hraw
  exact inv_nonneg.mpr ENNReal.toReal_nonneg

/-- The centered cube oscillation of a coordinate is bounded by the centered
native-vector mean `L²` seminorm on the same cube. -/
theorem centeredCubeL2Oscillation_coordinate_le_centeredVectorMeanL2
    {g : Vec d → Vec d} (z : Vec d) {r : ℝ}
    (hg : MemVectorL2On (centeredAxisCube z r) g) (i : Fin d) :
    centeredCubeL2Oscillation (fun x => g x i) z r ≤
      centeredVectorMeanL2 (centeredAxisCube z r) g := by
  rw [centeredCubeL2Oscillation,
    integral_normalizedVolumeOn_eq_integralAverage]
  simpa only [centeredCubeAverage, vectorIntegralAverage_apply] using
    sqrt_integralAverage_sq_sub_coordinate_mean_le_centeredVectorMeanL2
      hg (lt_top_iff_ne_top.mpr (volume_centeredAxisCube_ne_top z r)) i

/-- Each coordinate's centered cube oscillation is controlled by the vector
centered mean `L²` seminorm on the standard enclosing Euclidean ball. -/
theorem centeredCubeL2Oscillation_coordinate_le_enclosingBall_vectorMeanL2
    (hd : 0 < d) {g : Vec d → Vec d} (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hg : MemVectorL2On (euclideanBall z (2 * Real.sqrt d * r)) g)
    (i : Fin d) :
    centeredCubeL2Oscillation (fun x => g x i) z r ≤
      Real.sqrt ((Real.sqrt d) ^ d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal) *
        centeredVectorMeanL2 (euclideanBall z (2 * Real.sqrt d * r)) g := by
  let Q := centeredAxisCube z r
  let B := euclideanBall z (2 * Real.sqrt d * r)
  have hQB : Q ⊆ B := by
    simpa only [Q, B] using centeredAxisCube_subset_euclideanBall hd z hr
  have hgQ : MemVectorL2On Q g := fun j =>
    (hg j).mono_measure (Measure.restrict_mono hQB le_rfl)
  have hmono := centeredVectorMeanL2_mono_set hQB hg
    (by simpa only [Q] using volume_centeredAxisCube_pos z hr)
    (by
      exact lt_top_iff_ne_top.mpr
        (by simpa only [Q] using volume_centeredAxisCube_ne_top z r))
    (by
      simpa only [B] using
        volume_euclideanBall_pos z (by positivity : 0 < 2 * Real.sqrt d * r))
    (by
      exact lt_top_iff_ne_top.mpr
        (by
          simpa only [B] using volume_euclideanBall_ne_top z
            (by positivity : 0 ≤ 2 * Real.sqrt d * r)))
  rw [Real.sqrt_div ENNReal.toReal_nonneg] at hmono
  have hratio :
      Real.sqrt (volume B).toReal / Real.sqrt (volume Q).toReal =
        Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
    simpa only [Q, B] using sqrt_volume_enclosingBall_div_cube z hr hd
  rw [hratio] at hmono
  exact (centeredCubeL2Oscillation_coordinate_le_centeredVectorMeanL2
    z hgQ i).trans hmono

end

end PDE
