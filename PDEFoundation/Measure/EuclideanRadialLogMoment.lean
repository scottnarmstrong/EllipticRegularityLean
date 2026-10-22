module

public import PDEFoundation.Analysis.HilbertRadialLogMoment
public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Sobolev.Mean

/-! # Native Euclidean radial logarithmic moments -/

@[expose] public section

namespace PDE

open MeasureTheory Metric

noncomputable section

/-- Positive logarithmic powers are genuinely integrable on native round
balls in every positive dimension. -/
theorem integrableOn_neg_log_vecEuclideanNorm_div_euclideanBall
    {d : ℕ} (hd : 0 < d) {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    IntegrableOn
      (fun x : Vec d => (-Real.log (vecEuclideanNorm x / R)) ^ p)
      (euclideanBall 0 R) := by
  let : NeZero d := ⟨hd.ne'⟩
  have htransport := Internal.measurePreserving_toHilbert.integrableOn_comp_preimage
    (Internal.toHilbert : Vec d ≃L[ℝ] HilbertVec d).toHomeomorph.measurableEmbedding
    (f := fun z : HilbertVec d => (-Real.log (‖z‖ / R)) ^ p)
    (s := Metric.ball 0 R)
  have hpre : Internal.toHilbert ⁻¹' Metric.ball (0 : HilbertVec d) R =
      euclideanBall (0 : Vec d) R := by
    simpa only [map_zero] using Internal.preimage_ball_toHilbert (0 : Vec d) hR
  rw [hpre] at htransport
  have hfun : (fun z : HilbertVec d => (-Real.log (‖z‖ / R)) ^ p) ∘
      Internal.toHilbert =
      fun x : Vec d => (-Real.log (vecEuclideanNorm x / R)) ^ p := by
    funext x
    simp only [Function.comp_apply, Internal.toHilbert_apply,
      ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  rw [hfun] at htransport
  rw [htransport]
  exact Internal.integrableOn_radialLogMoment_hilbert hR hp

/-- Exact normalized logarithmic moment on a native round ball. -/
theorem integralAverage_neg_log_vecEuclideanNorm_div_euclideanBall
    {d : ℕ} (hd : 0 < d) {R p : ℝ} (hR : 0 < R) (hp : 0 < p) :
    integralAverage (euclideanBall (0 : Vec d) R)
        (fun x => (-Real.log (vecEuclideanNorm x / R)) ^ p) =
      Real.Gamma (p + 1) / (d : ℝ) ^ p := by
  let : NeZero d := ⟨hd.ne'⟩
  have hpreR : Internal.toHilbert ⁻¹' Metric.ball (0 : HilbertVec d) R =
      euclideanBall (0 : Vec d) R := by
    simpa only [map_zero] using Internal.preimage_ball_toHilbert (0 : Vec d) hR
  have hvolR : volume (euclideanBall (0 : Vec d) R) =
      volume (Metric.ball (0 : HilbertVec d) R) := by
    rw [← hpreR]
    exact Internal.measurePreserving_toHilbert.measure_preimage
      measurableSet_ball.nullMeasurableSet
  have hpreOne : Internal.toHilbert ⁻¹' Metric.ball (0 : HilbertVec d) 1 =
      euclideanBall (0 : Vec d) 1 := by
    simpa only [map_zero] using
      Internal.preimage_ball_toHilbert (0 : Vec d) (by norm_num)
  have hvolOne : volume (euclideanBall (0 : Vec d) 1) =
      volume (Metric.ball (0 : HilbertVec d) 1) := by
    rw [← hpreOne]
    exact Internal.measurePreserving_toHilbert.measure_preimage
      measurableSet_ball.nullMeasurableSet
  have hint : (∫ x in euclideanBall (0 : Vec d) R,
      (-Real.log (vecEuclideanNorm x / R)) ^ p) =
      ∫ z in Metric.ball (0 : HilbertVec d) R,
        (-Real.log (‖z‖ / R)) ^ p := by
    rw [← hpreR]
    have h := Internal.measurePreserving_toHilbert.setIntegral_preimage_emb
      Internal.toHilbert.toHomeomorph.measurableEmbedding
      (fun z : HilbertVec d => (-Real.log (‖z‖ / R)) ^ p)
      (Metric.ball (0 : HilbertVec d) R)
    simpa only [Internal.toHilbert_apply,
      ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec] using h
  unfold integralAverage
  rw [hvolR, hint, Internal.integral_radialLogMoment_hilbert hR hp]
  rw [← hvolR, ← hvolOne]
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) hR]
  have hunit : (volume (euclideanBall (0 : Vec d) 1)).toReal ≠ 0 :=
    ne_of_gt (volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num))
  have hRpow : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdp : (d : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos hdR p).ne'
  have hdstep : (d : ℝ) ^ (p + 1) = (d : ℝ) ^ p * d := by
    rw [Real.rpow_add hdR, Real.rpow_one]
  rw [hdstep, Real.rpow_natCast R d]
  field_simp

end

end PDE
