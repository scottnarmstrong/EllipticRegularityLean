module

public import PDEFoundation.Regularity.FieldHolder
public import PDEFoundation.Sobolev.H1.MeanEnergy
public import PDEFoundation.Sobolev.H1.VectorL2Bounds

/-! # Freezing Hölder fields at the center of a round ball -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- An almost everywhere Euclidean bound controls the normalized vector
mean-square magnitude with constant one. -/
theorem sqrt_integralAverage_vecNormSq_le_of_ae_bound
    {U : Set (Vec d)} {g : Vec d → Vec d} (hg : MemVectorL2On U g)
    (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ x ∂volumeOn U, vecEuclideanNorm (g x) ≤ K) :
    Real.sqrt (integralAverage U (fun x => vecNormSq (g x))) ≤ K := by
  have hsq : ∀ᵐ x ∂volumeOn U, vecNormSq (g x) ≤ K ^ 2 := by
    filter_upwards [hbound] with x hx
    rw [← vecEuclideanNorm_sq]
    exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) hx 2
  have hint := integral_mono_ae (integrableOn_vecNormSq_of_memVectorL2On hg)
    (integrableOn_const hUtop.ne) hsq
  have hv : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUpos.ne' hUtop.ne).ne'
  have havg : integralAverage U (fun x => vecNormSq (g x)) ≤ K ^ 2 := by
    unfold integralAverage
    calc
      (volume U).toReal⁻¹ * (∫ x in U, vecNormSq (g x)) ≤
          (volume U).toReal⁻¹ * (∫ _x in U, K ^ 2) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = K ^ 2 := by
        rw [setIntegral_const, smul_eq_mul]
        change (volume U).toReal⁻¹ * ((volume U).toReal * K ^ 2) = K ^ 2
        rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
  exact (Real.sqrt_le_sqrt havg).trans_eq (Real.sqrt_sq hK)

/-- On a ball, freezing a Hölder vector field at its center leaves a
pointwise error at most `K * R^α`. -/
theorem EuclideanFieldHolderSeminormLE.sub_center_bound
    {U : Set (Vec d)} {F : Vec d → Vec d} {α K R : ℝ} {z : Vec d}
    (hF : EuclideanFieldHolderSeminormLE U F α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hR : 0 < R)
    (hz : z ∈ U) (hball : euclideanBall z R ⊆ U)
    {x : Vec d} (hx : x ∈ euclideanBall z R) :
    vecEuclideanNorm (F x - F z) ≤ K * R ^ α :=
  (hF x (hball hx) z hz).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (vecEuclideanNorm_nonneg _)
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx).le hα) hK)

/-- The same freezing estimate in the actual Euclidean operator norm. -/
theorem EuclideanMatrixHolderSeminormLE.sub_center_bound
    {U : Set (Vec d)} {a : CoeffField d} {α K R : ℝ} {z : Vec d}
    (ha : EuclideanMatrixHolderSeminormLE U a α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hR : 0 < R)
    (hz : z ∈ U) (hball : euclideanBall z R ⊆ U)
    {x : Vec d} (hx : x ∈ euclideanBall z R) :
    IsMatrixPerturbationLE (K * R ^ α) (a x) (a z) := by
  intro ξ
  exact (ha x (hball hx) z hz ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (vecEuclideanNorm_nonneg _)
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx).le hα) hK)
      (vecEuclideanNorm_nonneg ξ))

/-- Actual `L²` membership upgrades the pointwise freezing bound to the
normalized forcing bound used by harmonic replacement. -/
theorem EuclideanFieldHolderSeminormLE.sqrt_mean_sub_center_le
    {U : Set (Vec d)} {F : Vec d → Vec d} {α K R : ℝ} {z : Vec d}
    (hF : EuclideanFieldHolderSeminormLE U F α K)
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hR : 0 < R)
    (hz : z ∈ U) (hball : euclideanBall z R ⊆ U)
    (hL2 : MemVectorL2On (euclideanBall z R) (fun x => F x - F z)) :
    Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (F x - F z))) ≤ K * R ^ α := by
  apply sqrt_integralAverage_vecNormSq_le_of_ae_bound hL2
    (volume_euclideanBall_pos z hR) (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top z hR.le))
    (mul_nonneg hK (Real.rpow_nonneg hR.le _))
  exact (ae_restrict_mem (isOpen_euclideanBall z R).measurableSet).mono
    (fun _ hx => hF.sub_center_bound hα hK hR hz hball hx)

/-- Hölder continuity supplies the actual `L²` membership of the
forcing error on a ball; no integrability certificate is an extra premise. -/
theorem EuclideanFieldHolderSeminormLE.memVectorL2On_sub_center
    {U : Set (Vec d)} {F : Vec d → Vec d} {α K R : ℝ} {z : Vec d}
    (hF : EuclideanFieldHolderSeminormLE U F α K)
    (hα : 0 < α) (hK : 0 ≤ K) (hR : 0 < R)
    (hz : z ∈ U) (hball : euclideanBall z R ⊆ U) :
    MemVectorL2On (euclideanBall z R) (fun x => F x - F z) := by
  let : IsFiniteMeasure (volumeOn (euclideanBall z R)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_ne_top z hR.le)
  intro i
  have hc : ContinuousOn (fun x => F x i - F z i) (euclideanBall z R) :=
    (((hF.coordinate i).continuousOn hα hK).mono hball).sub continuousOn_const
  apply MemLp.of_bound (hc.aestronglyMeasurable
    (isOpen_euclideanBall z R).measurableSet) (K * R ^ α)
  filter_upwards [ae_restrict_mem (isOpen_euclideanBall z R).measurableSet] with x hx
  exact (abs_apply_le_vecEuclideanNorm (F x - F z) i).trans
    (hF.sub_center_bound hα.le hK hR hz hball hx)

/-- The normalized freezing estimate with its integrability premise
discharged by the actual Hölder hypothesis. -/
theorem EuclideanFieldHolderSeminormLE.sqrt_mean_sub_center_le_of_pos
    {U : Set (Vec d)} {F : Vec d → Vec d} {α K R : ℝ} {z : Vec d}
    (hF : EuclideanFieldHolderSeminormLE U F α K)
    (hα : 0 < α) (hK : 0 ≤ K) (hR : 0 < R)
    (hz : z ∈ U) (hball : euclideanBall z R ⊆ U) :
    Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (F x - F z))) ≤ K * R ^ α :=
  hF.sqrt_mean_sub_center_le hα.le hK hR hz hball
    (hF.memVectorL2On_sub_center hα hK hR hz hball)

end PDE
