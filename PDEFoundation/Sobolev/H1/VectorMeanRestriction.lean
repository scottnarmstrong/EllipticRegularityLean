module

public import PDEFoundation.Sobolev.H1.VectorMeanOscillation

/-!
# Restriction bounds for centered vector mean `L²`

These consequences of the exact vector variance identity compare centered
mean-square oscillations across nested finite-volume domains and with the
uncentered Euclidean energy.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Restricting a centered vector mean `L²` seminorm to a positive-volume
subset costs exactly the square root of the volume ratio. -/
theorem centeredVectorMeanL2_mono_set
    {V U : Set (Vec d)} (hVU : V ⊆ U)
    {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    (hVpos : 0 < volume V) (hVtop : volume V < ∞)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    centeredVectorMeanL2 V g ≤
      Real.sqrt ((volume U).toReal / (volume V).toReal) *
        centeredVectorMeanL2 U g := by
  have hgV : MemVectorL2On V g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hVU le_rfl)
  have hcenterU := memVectorL2On_sub_const hg hUtop (vectorIntegralAverage U g)
  have hmin :
      (∫ x in V, vecNormSq (g x - vectorIntegralAverage V g) ∂volume) ≤
        ∫ x in V, vecNormSq (g x - vectorIntegralAverage U g) ∂volume :=
    setIntegral_vecNormSq_sub_vectorIntegralAverage_le
      hgV hVpos hVtop (vectorIntegralAverage U g)
  have hrestrict :
      (∫ x in V, vecNormSq (g x - vectorIntegralAverage U g) ∂volume) ≤
        ∫ x in U, vecNormSq (g x - vectorIntegralAverage U g) ∂volume :=
    setIntegral_vecNormSq_mono_set hVU hcenterU
  have hraw := hmin.trans hrestrict
  have hVreal : 0 < (volume V).toReal :=
    ENNReal.toReal_pos hVpos.ne' hVtop.ne
  have hUreal : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUpos.ne' hUtop.ne
  unfold centeredVectorMeanL2
  simp only [sqrt_integralAverage_vecNormSq_eq]
  have hroot := Real.sqrt_le_sqrt hraw
  calc
    Real.sqrt (∫ x in V,
        vecNormSq (g x - vectorIntegralAverage V g) ∂volume) /
        Real.sqrt (volume V).toReal ≤
      Real.sqrt (∫ x in U,
        vecNormSq (g x - vectorIntegralAverage U g) ∂volume) /
        Real.sqrt (volume V).toReal :=
      div_le_div_of_nonneg_right hroot (Real.sqrt_nonneg _)
    _ = Real.sqrt ((volume U).toReal / (volume V).toReal) *
        (Real.sqrt (∫ x in U,
          vecNormSq (g x - vectorIntegralAverage U g) ∂volume) /
            Real.sqrt (volume U).toReal) := by
      rw [Real.sqrt_div ENNReal.toReal_nonneg]
      field_simp [(Real.sqrt_pos.mpr hVreal).ne',
        (Real.sqrt_pos.mpr hUreal).ne']

/-- Centering at the vector integral average can only decrease normalized
Euclidean `L²` energy. -/
theorem centeredVectorMeanL2_le_sqrt_integralAverage_vecNormSq
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    centeredVectorMeanL2 U g ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (g x))) := by
  have hraw := setIntegral_vecNormSq_sub_vectorIntegralAverage_le
    hg hUpos hUtop (0 : Vec d)
  have hzero : (fun x => vecNormSq (g x - (0 : Vec d))) =
      fun x => vecNormSq (g x) := by
    funext x
    simp
  rw [hzero] at hraw
  unfold centeredVectorMeanL2
  simp only [sqrt_integralAverage_vecNormSq_eq]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hraw)
    (Real.sqrt_nonneg _)

/-- The Euclidean magnitude of the vector integral average is bounded by the
root mean-square Euclidean magnitude. -/
theorem vecEuclideanNorm_vectorIntegralAverage_le_sqrt_integralAverage_vecNormSq
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2On U g)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞) :
    vecEuclideanNorm (vectorIntegralAverage U g) ≤
      Real.sqrt (integralAverage U (fun x => vecNormSq (g x))) := by
  have hidentity := setIntegral_vecNormSq_sub_eq_centered_add
    hg hUpos hUtop (0 : Vec d)
  have hcenterNonneg :
      0 ≤ ∫ x in U,
        vecNormSq (g x - vectorIntegralAverage U g) ∂volume :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hmeanTerm :
      (volume U).toReal * vecNormSq (vectorIntegralAverage U g) ≤
        ∫ x in U, vecNormSq (g x) ∂volume := by
    have hzeroLeft : (fun x => vecNormSq (g x - (0 : Vec d))) =
        fun x => vecNormSq (g x) := by
      funext x
      simp
    have hzeroMean :
        vecNormSq (vectorIntegralAverage U g - (0 : Vec d)) =
          vecNormSq (vectorIntegralAverage U g) := by simp
    rw [hzeroLeft, hzeroMean] at hidentity
    rw [hidentity]
    exact le_add_of_nonneg_left hcenterNonneg
  have hUreal : 0 < (volume U).toReal :=
    ENNReal.toReal_pos hUpos.ne' hUtop.ne
  have hsq : vecNormSq (vectorIntegralAverage U g) ≤
      (∫ x in U, vecNormSq (g x) ∂volume) / (volume U).toReal := by
    apply (le_div_iff₀ hUreal).2
    simpa only [mul_comm] using hmeanTerm
  unfold vecEuclideanNorm
  rw [sqrt_integralAverage_vecNormSq_eq]
  calc
    Real.sqrt (vecNormSq (vectorIntegralAverage U g)) ≤
        Real.sqrt ((∫ x in U, vecNormSq (g x) ∂volume) /
          (volume U).toReal) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ x in U, vecNormSq (g x) ∂volume) /
        Real.sqrt (volume U).toReal := by
      rw [Real.sqrt_div (integral_nonneg fun x => vecNormSq_nonneg _)]

end

end PDE
