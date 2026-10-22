module

public import PDEFoundation.Sobolev.H1.VectorMeanRestriction

/-! # Exact decomposition of vector mean energy -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The normalized Euclidean energy is the sum of the centered energy and
the squared magnitude of the vector mean. -/
theorem integralAverage_vecNormSq_eq_centered_add_mean
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    integralAverage U (fun x => vecNormSq (g x)) =
      integralAverage U (fun x => vecNormSq (g x - vectorIntegralAverage U g)) +
        vecNormSq (vectorIntegralAverage U g) := by
  have hraw := setIntegral_vecNormSq_sub_eq_centered_add hg hUpos hUtop (0 : Vec d)
  simp only [sub_zero] at hraw
  have hv : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUpos.ne' hUtop.ne).ne'
  unfold integralAverage
  rw [hraw, mul_add, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

/-- Full root mean-square size is at most the sum of mean magnitude and
centered root mean-square oscillation. -/
theorem sqrt_integralAverage_vecNormSq_le_mean_add_centered
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g) (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (g x))) ≤
      vecEuclideanNorm (vectorIntegralAverage U g) + centeredVectorMeanL2 U g := by
  have hcenter : 0 ≤ integralAverage U
      (fun x => vecNormSq (g x - vectorIntegralAverage U g)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => vecNormSq_nonneg _)
  have hsq := Real.sq_sqrt hcenter
  have hmean := vecEuclideanNorm_sq (vectorIntegralAverage U g)
  have hc : 0 ≤ centeredVectorMeanL2 U g := Real.sqrt_nonneg _
  have hm := vecEuclideanNorm_nonneg (vectorIntegralAverage U g)
  apply (Real.sqrt_le_iff).mpr
  refine ⟨add_nonneg hm hc, ?_⟩
  rw [integralAverage_vecNormSq_eq_centered_add_mean hg hUpos hUtop]
  change integralAverage U (fun x => vecNormSq (g x - vectorIntegralAverage U g)) +
      vecNormSq (vectorIntegralAverage U g) ≤
    (vecEuclideanNorm (vectorIntegralAverage U g) +
      Real.sqrt (integralAverage U (fun x => vecNormSq (g x - vectorIntegralAverage U g)))) ^ 2
  nlinarith only [hsq, hmean, mul_nonneg hm (Real.sqrt_nonneg
    (integralAverage U (fun x => vecNormSq (g x - vectorIntegralAverage U g))))]

end PDE
