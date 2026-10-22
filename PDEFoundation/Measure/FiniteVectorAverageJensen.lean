module

public import PDEFoundation.Measure.FiniteVectorMean

/-! # Quadratic Jensen inequality for coordinatewise finite vector means -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- The squared Euclidean norm of a coordinatewise mean is bounded by the
normalized mean squared Euclidean deviation. Source and target dimensions are
independent, and the statement includes the zero target dimension. -/
theorem vecNormSq_coordinateVectorAverage_sub_le_integralAverage
    {d m : ℕ} {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : Vec m) :
    vecNormSq (coordinateVectorAverage U g - c) ≤
      integralAverage U (fun x => vecNormSq (g x - c)) := by
  have hvol : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have hid :=
    setIntegral_vecNormSq_sub_eq_coordinateVectorAverage_add hg hUpos hUtop c
  have hcenter :
      0 ≤ ∫ x in U, vecNormSq (g x - coordinateVectorAverage U g) ∂volume :=
    integral_nonneg_of_ae (ae_of_all _ fun x => vecNormSq_nonneg _)
  have hproduct :
      (volume U).toReal * vecNormSq (coordinateVectorAverage U g - c) ≤
        ∫ x in U, vecNormSq (g x - c) ∂volume := by
    linarith
  unfold integralAverage
  calc
    vecNormSq (coordinateVectorAverage U g - c) =
        (volume U).toReal⁻¹ *
          ((volume U).toReal * vecNormSq (coordinateVectorAverage U g - c)) := by
      field_simp
    _ ≤ (volume U).toReal⁻¹ *
        ∫ x in U, vecNormSq (g x - c) ∂volume :=
      mul_le_mul_of_nonneg_left hproduct (inv_nonneg.mpr hvol.le)

/-- Square root form of quadratic Jensen for the Euclidean vector norm. -/
theorem vecEuclideanNorm_coordinateVectorAverage_sub_le_sqrt_integralAverage
    {d m : ℕ} {U : Set (Vec d)} {g : Vec d → Vec m}
    (hg : ∀ i : Fin m, MemLp (fun x => g x i) 2 (volumeOn U))
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) (c : Vec m) :
    vecEuclideanNorm (coordinateVectorAverage U g - c) ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (g x - c))) := by
  unfold vecEuclideanNorm
  exact Real.sqrt_le_sqrt
    (vecNormSq_coordinateVectorAverage_sub_le_integralAverage hg hUpos hUtop c)

end PDE
