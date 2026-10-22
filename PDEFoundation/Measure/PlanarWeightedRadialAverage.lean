module

public import PDEFoundation.Ambient.PlanarRadialProjection
public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.LinearNormalizedVolume
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Sobolev.Mean
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace PDE
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private def quarterTurn : Vec 2 ≃ₗ[ℝ] Vec 2 where
  toFun x := ![-x 1, x 0]
  invFun x := ![x 1, -x 0]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp

private def quarterTurnContinuous : Vec 2 ≃L[ℝ] Vec 2 :=
  quarterTurn.toContinuousLinearEquiv

private theorem quarterTurn_normSq (x : Vec 2) :
    vecNormSq (quarterTurnContinuous x) = vecNormSq x := by
  simp [quarterTurnContinuous, quarterTurn, vecNormSq, vecDot, Fin.sum_univ_two]
  ring

private theorem quarterTurn_norm (x : Vec 2) :
    vecEuclideanNorm (quarterTurnContinuous x) = vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  rw [quarterTurn_normSq]

private theorem quarterTurn_image_ball {R : ℝ} (hR : 0 < R) :
    quarterTurnContinuous '' euclideanBall 0 R = euclideanBall 0 R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hy ⊢
    simpa only [sub_zero, quarterTurn_norm] using hy
  · intro hx
    refine ⟨quarterTurnContinuous.symm x, ?_, quarterTurnContinuous.apply_symm_apply x⟩
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR] at hx ⊢
    simp only [sub_zero] at hx ⊢
    have hn := quarterTurn_norm (quarterTurnContinuous.symm x)
    rw [quarterTurnContinuous.apply_symm_apply] at hn
    exact hn.symm.trans_lt hx

/-- Radial integration in the plane assigns half of a radial weight to each
coordinate projection. -/
theorem integralAverage_planar_coordinate_square_ratio_mul_radial
    {R : ℝ} (hR : 0 < R) (h : ℝ → ℝ)
    (hh : IntegrableOn (fun x : Vec 2 => h (vecEuclideanNorm x))
      (euclideanBall 0 R)) :
    integralAverage (euclideanBall (0 : Vec 2) R)
      (fun x => x 0 ^ 2 / vecNormSq x * h (vecEuclideanNorm x)) =
      (1 / 2 : ℝ) * integralAverage (euclideanBall (0 : Vec 2) R)
        (fun x => h (vecEuclideanNorm x)) := by
  let μ := normalizedVolumeOn (euclideanBall (0 : Vec 2) R)
  have hhi : Integrable (fun x : Vec 2 => h (vecEuclideanNorm x)) μ :=
    hh.smul_measure (ENNReal.inv_ne_top.mpr
      (ne_of_gt (volume_euclideanBall_pos _ hR)))
  have hratio (i : Fin 2) : ∀ x : Vec 2, ‖x i ^ 2 / vecNormSq x‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (vecNormSq_nonneg _))]
    by_cases hx : x = 0
    · subst x; simp [vecNormSq, vecDot]
    · have hq : 0 < vecNormSq x :=
        lt_of_le_of_ne (vecNormSq_nonneg x) (Ne.symm (vecNormSq_eq_zero_iff.not.mpr hx))
      exact (div_le_one hq).mpr (sq_apply_le_vecNormSq x i)
  have hwi (i : Fin 2) : Integrable
      (fun x : Vec 2 => x i ^ 2 / vecNormSq x * h (vecEuclideanNorm x)) μ := by
    exact hhi.bdd_mul
      (((measurable_pi_apply i).pow_const 2).div continuous_vecNormSq.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (hratio i))
  have hmp : MeasurePreserving quarterTurnContinuous μ μ := by
    have hm := measurePreserving_linearEquiv_normalizedVolumeOn
      quarterTurnContinuous (euclideanBall (0 : Vec 2) R)
    rw [quarterTurn_image_ball hR] at hm
    exact hm
  have heq : (∫ x : Vec 2, x 1 ^ 2 / vecNormSq x * h (vecEuclideanNorm x) ∂μ) =
      ∫ x : Vec 2, x 0 ^ 2 / vecNormSq x * h (vecEuclideanNorm x) ∂μ := by
    have ht := hmp.integral_comp quarterTurnContinuous.toHomeomorph.measurableEmbedding
      (fun x : Vec 2 => x 0 ^ 2 / vecNormSq x * h (vecEuclideanNorm x))
    have hcoord (x : Vec 2) : quarterTurnContinuous x 0 = -x 1 := rfl
    simpa only [Function.comp_apply, quarterTurn_normSq, quarterTurn_norm, hcoord, neg_sq] using ht
  have hne : ∀ᵐ x ∂μ, x ≠ (0 : Vec 2) := by
    rw [ae_iff]
    simp only [not_ne_iff]
    change μ {0} = 0
    simp only [μ, normalizedVolumeOn, Measure.smul_apply]
    have hz : (volumeOn (euclideanBall (0 : Vec 2) R)) {0} = 0 := by
      rw [volumeOn, Measure.restrict_apply (measurableSet_singleton (0 : Vec 2))]
      exact measure_mono_null (inter_subset_left (s := ({0} : Set (Vec 2))))
        (measure_singleton (μ := volume) (0 : Vec 2))
    rw [hz, smul_zero]
  have hsum :
      (∫ x : Vec 2, x 0 ^ 2 / vecNormSq x * h (vecEuclideanNorm x) ∂μ) +
      (∫ x : Vec 2, x 1 ^ 2 / vecNormSq x * h (vecEuclideanNorm x) ∂μ) =
      ∫ x : Vec 2, h (vecEuclideanNorm x) ∂μ := by
    rw [← integral_add (hwi 0) (hwi 1)]
    apply integral_congr_ae
    filter_upwards [hne] with x hx
    have hq := vecNormSq_eq_zero_iff.not.mpr hx
    have hqs : vecNormSq x = x 0 ^ 2 + x 1 ^ 2 := by
      simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    rw [← add_mul, ← add_div, ← hqs, div_self hq, one_mul]
  rw [heq] at hsum
  simp_rw [← integral_normalizedVolumeOn_eq_integralAverage]
  change (∫ x : Vec 2, x 0 ^ 2 / vecNormSq x * h (vecEuclideanNorm x) ∂μ) =
    (1 / 2 : ℝ) * ∫ x : Vec 2, h (vecEuclideanNorm x) ∂μ
  linarith only [hsum]

end
end PDE
