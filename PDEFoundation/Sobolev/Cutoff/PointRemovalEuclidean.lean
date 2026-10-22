module

public import PDEFoundation.Sobolev.Cutoff.PointRemoval

/-! # Euclidean-magnitude bounds for point-removal cutoffs -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Direct radius-dependent `L²` bound for the scalar Euclidean magnitude of
point-removal cutoff gradients. -/
theorem pointRemovalCutoff_euclideanGradient_eLpNorm_two_le
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    eLpNorm
      (fun x => vecEuclideanNorm
        (classicalGradient (pointRemovalCutoff (d := d) ε) x))
      2 volume ≤
      ENNReal.ofReal (32 / ε) *
        volume (euclideanBall (0 : Vec d) (2 * ε)) ^ (1 / (2 : ℝ)) := by
  let f : Vec d → ℝ := fun x => vecEuclideanNorm
    (classicalGradient (pointRemovalCutoff (d := d) ε) x)
  have hsupport : Function.support f ⊆ euclideanBall (0 : Vec d) (2 * ε) := by
    intro x hx
    by_contra hxb
    have hr : 2 * ε ≤ vecEuclideanNorm x := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt
        (by positivity : 0 < 2 * ε)] at hxb
      simpa using not_lt.mp hxb
    apply hx
    change vecEuclideanNorm
      (classicalGradient (pointRemovalCutoff (d := d) ε) x) = 0
    rw [pointRemovalCutoff_gradient_zero hε hr]
    exact vecEuclideanNorm_eq_zero_iff.mpr rfl
  have hzero : Function.support (0 : Vec d → ℝ) ⊆
      euclideanBall (0 : Vec d) (2 * ε) := by simp
  have hfm : AEStronglyMeasurable (f - (0 : Vec d → ℝ)) volume := by
    rw [sub_zero]
    exact continuous_vecEuclideanNorm.comp_aestronglyMeasurable
      (pointRemovalCutoff_gradient_memLp_two hε).aestronglyMeasurable
  have hb := eLpNorm_sub_le_of_dist_bdd (μ := volume) (p := (2 : ℝ≥0∞))
    (by norm_num) (measurableSet_euclideanBall (0 : Vec d) (2 * ε)).nullMeasurableSet
    (c := 32 / ε) (by positivity)
    (f := f) (g := (0 : Vec d → ℝ)) hfm
    (fun x => by
      rw [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (vecEuclideanNorm_nonneg _)]
      exact pointRemovalCutoff_gradient_bound hε x)
    hsupport hzero
  simpa [f] using hb

/-- The Euclidean magnitude of the point-removal cutoff gradient belongs to
`L²` globally. -/
theorem pointRemovalCutoff_euclideanGradient_memLp_two
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    MemLp
      (fun x => vecEuclideanNorm
        (classicalGradient (pointRemovalCutoff (d := d) ε) x))
      2 volume := by
  have hsmooth := canonicalBallCutoff_smooth (x₀ := (0 : Vec d)) hε.le
    (by linarith : ε < 2 * ε)
  have hcont : Continuous
      (fun x => vecEuclideanNorm
        (classicalGradient (pointRemovalCutoff (d := d) ε) x)) :=
    continuous_vecEuclideanNorm.comp
      (PDE.ContDiff.continuous_classicalGradient (hsmooth.of_le (by simp)))
  exact (pointRemovalCutoff_euclideanGradient_eLpNorm_two_le hε).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (volume_euclideanBall_ne_top (0 : Vec d) (by positivity : 0 ≤ 2 * ε))))

/-- In dimensions at least two, the scalar Euclidean-magnitude `L²` norm of
the point-removal cutoff gradient is bounded uniformly in its radius. -/
theorem pointRemovalCutoff_euclideanGradient_eLpNorm_two_uniform
    {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eLpNorm
      (fun x => vecEuclideanNorm
        (classicalGradient (pointRemovalCutoff (d := d) ε) x))
      2 volume ≤
      ENNReal.ofReal 32 *
        (ENNReal.ofReal ((2 : ℝ) ^ d) *
          volume (euclideanBall (0 : Vec d) 1)) ^ (1 / (2 : ℝ)) := by
  refine (pointRemovalCutoff_euclideanGradient_eLpNorm_two_le hε).trans ?_
  rw [volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec d)
    (by positivity : 0 < 2 * ε)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hepow : ε ^ d ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1 hd
  have hpow : (2 * ε) ^ d ≤ (2 : ℝ) ^ d * ε ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hepow (pow_nonneg (by norm_num) d)
  have hroot : ENNReal.ofReal ((2 * ε) ^ d) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ d) * ε ^ 2) ^ (1 / (2 : ℝ)) := by
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hpow) (by norm_num)
  calc
    ENNReal.ofReal (32 / ε) *
        (ENNReal.ofReal ((2 * ε) ^ d) ^ (1 / (2 : ℝ)) *
          volume (euclideanBall (0 : Vec d) 1) ^ (1 / (2 : ℝ))) ≤
      ENNReal.ofReal (32 / ε) *
        (ENNReal.ofReal (((2 : ℝ) ^ d) * ε ^ 2) ^ (1 / (2 : ℝ)) *
          volume (euclideanBall (0 : Vec d) 1) ^ (1 / (2 : ℝ))) := by gcongr
    _ = ENNReal.ofReal 32 *
        (ENNReal.ofReal ((2 : ℝ) ^ d) *
          volume (euclideanBall (0 : Vec d) 1)) ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.ofReal_mul (pow_nonneg (by norm_num) d),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hε.le]
      have he : (ENNReal.ofReal ε ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) =
          ENNReal.ofReal ε := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      rw [he, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      calc
        ENNReal.ofReal (32 / ε) *
            (ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / (2 : ℝ)) *
              ENNReal.ofReal ε *
                volume (euclideanBall (0 : Vec d) 1) ^ (1 / (2 : ℝ))) =
            (ENNReal.ofReal (32 / ε) * ENNReal.ofReal ε) *
              (ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / (2 : ℝ)) *
                volume (euclideanBall (0 : Vec d) 1) ^ (1 / (2 : ℝ))) := by
          ac_rfl
        _ = ENNReal.ofReal 32 *
              (ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / (2 : ℝ)) *
                volume (euclideanBall (0 : Vec d) 1) ^ (1 / (2 : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 32 / ε)]
          congr 2
          field_simp

end

end PDE
