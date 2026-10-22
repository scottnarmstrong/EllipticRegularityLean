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

private theorem quarterTurn_reflection_neg (x : Vec 2) (hx : x ≠ 0) :
    radialReflectionMatrix (quarterTurnContinuous x) = -radialReflectionMatrix x := by
  have hq : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  ext i j
  simp only [radialReflectionMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply, radialProjectionMatrix_apply, quarterTurn_normSq]
  fin_cases i <;> fin_cases j <;>
    simp [quarterTurnContinuous, quarterTurn] <;> field_simp [hq] <;>
    simp [vecNormSq, vecDot, Fin.sum_univ_two] <;> ring

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

private theorem integral_radialReflectionMatrix_normalized_ball {R : ℝ}
    (hR : 0 < R) (i j : Fin 2) :
    ∫ x, radialReflectionMatrix x i j
      ∂normalizedVolumeOn (euclideanBall (0 : Vec 2) R) = 0 := by
  let μ := normalizedVolumeOn (euclideanBall (0 : Vec 2) R)
  have hmp : MeasurePreserving quarterTurnContinuous μ μ := by
    have hm := measurePreserving_linearEquiv_normalizedVolumeOn
      quarterTurnContinuous (euclideanBall (0 : Vec 2) R)
    rw [quarterTurn_image_ball hR] at hm
    exact hm
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
  have hc : (fun x => radialReflectionMatrix (quarterTurnContinuous x) i j) =ᵐ[μ]
      fun x => -radialReflectionMatrix x i j := by
    filter_upwards [hne] with x hx
    rw [quarterTurn_reflection_neg x hx]
    rfl
  have he := hmp.integral_comp quarterTurnContinuous.toHomeomorph.measurableEmbedding
    (fun x => radialReflectionMatrix x i j)
  have hneg : (∫ x, radialReflectionMatrix x i j ∂μ) =
      -(∫ x, radialReflectionMatrix x i j ∂μ) := by
    calc
      _ = ∫ x, radialReflectionMatrix (quarterTurnContinuous x) i j ∂μ := he.symm
      _ = ∫ x, -radialReflectionMatrix x i j ∂μ := integral_congr_ae hc
      _ = _ := integral_neg _
  linarith only [hneg]

/-- The exact round-ball average of the planar radial coefficient is the
identity matrix. -/
theorem integralAverage_one_add_planarRadialReflectionMatrix {R : ℝ}
    (hR : 0 < R) (δ : ℝ) :
    (fun i j => integralAverage (euclideanBall (0 : Vec 2) R)
      (fun x => ((1 : Mat 2) + δ • radialReflectionMatrix x) i j)) = (1 : Mat 2) := by
  let μ := normalizedVolumeOn (euclideanBall (0 : Vec 2) R)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      (volume_euclideanBall_pos _ hR)
      (lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ hR.le))
  ext i j
  rw [← integral_normalizedVolumeOn_eq_integralAverage]
  have hq : Integrable (fun x => radialReflectionMatrix x i j) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · have hm : Measurable (fun x : Vec 2 => radialReflectionMatrix x i j) := by
        simp only [radialReflectionMatrix, two_smul, Matrix.add_apply,
          Matrix.sub_apply, radialProjectionMatrix_apply]
        have hp := ((measurable_pi_apply i).mul (measurable_pi_apply j)).div
          continuous_vecNormSq.measurable
        exact (hp.add hp).sub measurable_const
      exact hm.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      have hc : matVecMul (radialReflectionMatrix x) (basisVec j) i =
          radialReflectionMatrix x i j := by
        fin_cases j <;> simp [matVecMul, basisVec_apply]
      rw [← hc]
      exact (abs_apply_le_vecEuclideanNorm _ i).trans (by
        rw [vecEuclideanNorm_matVecMul_radialReflectionMatrix,
          vecEuclideanNorm_basisVec])
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_add (integrable_const _) (hq.const_mul δ), integral_const_mul]
  change (∫ _ : Vec 2, (1 : Mat 2) i j ∂μ) +
    δ * (∫ x, radialReflectionMatrix x i j ∂μ) = _
  rw [integral_radialReflectionMatrix_normalized_ball hR i j]
  simp

end
end PDE
