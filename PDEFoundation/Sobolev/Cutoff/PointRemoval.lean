module

public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.LpPower

@[expose] public section

namespace PDE

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

/-- The canonical cutoff of the ball of radius `ε`, with outer radius `2ε`. -/
def pointRemovalCutoff {d : ℕ} (ε : ℝ) : Vec d → ℝ :=
  canonicalBallCutoff 0 ε (2 * ε)

@[simp]
theorem pointRemovalCutoff_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Vec d} (hx : 2 * ε ≤ vecEuclideanNorm x) :
    pointRemovalCutoff ε x = 0 := by
  by_contra hne
  have hsupp : x ∈ Function.support (pointRemovalCutoff ε) := hne
  have hts : x ∈ tsupport (pointRemovalCutoff ε) := subset_closure hsupp
  have hsub := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec d)) hε.le (by linarith : ε < 2 * ε)
  have hball := hsub hts
  have hlt := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : 0 < 2 * ε)).mp hball
  exact (not_lt_of_ge hx) (by simpa using hlt)

@[simp]
theorem pointRemovalCutoff_gradient_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Vec d} (hx : 2 * ε ≤ vecEuclideanNorm x) :
    classicalGradient (pointRemovalCutoff ε) x = 0 := by
  have hnot : x ∉ tsupport (pointRemovalCutoff ε) := by
    intro hts
    have hsub := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec d)) hε.le
      (by linarith : ε < 2 * ε)
    have hlt := (mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by positivity : 0 < 2 * ε)).mp (hsub hts)
    exact (not_lt_of_ge hx) (by simpa using hlt)
  have hd : fderiv ℝ (pointRemovalCutoff ε) x = 0 :=
    fderiv_of_notMem_tsupport ℝ hnot
  funext i
  rw [classicalGradient_apply, hd]
  exact zero_apply _

theorem pointRemovalCutoff_gradient_bound {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : Vec d) :
    vecEuclideanNorm (classicalGradient (pointRemovalCutoff ε) x) ≤ 32 / ε := by
  have h := canonicalBallCutoff_gradient_bound (x₀ := (0 : Vec d)) hε.le
      (by linarith : ε < 2 * ε) x
  simpa only [pointRemovalCutoff, show 2 * ε - ε = ε by ring] using h

private theorem pointRemovalCutoff_gradient_hasCompactSupport {d : ℕ} {ε : ℝ}
    (hε : 0 < ε) :
    HasCompactSupport (classicalGradient (pointRemovalCutoff (d := d) ε)) := by
  have hs := canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec d)) hε.le
    (by linarith : ε < 2 * ε)
  exact (hs.fderiv (𝕜 := ℝ)).mono (by
    intro x hx
    change classicalGradient (pointRemovalCutoff ε) x ≠ 0 at hx
    change fderiv ℝ (pointRemovalCutoff ε) x ≠ 0
    intro hz
    apply hx
    funext i
    rw [classicalGradient_apply, hz]
    exact zero_apply _)

theorem pointRemovalCutoff_gradient_memLp_two {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    MemLp (classicalGradient (pointRemovalCutoff (d := d) ε)) 2 volume := by
  have hsmooth := canonicalBallCutoff_smooth (x₀ := (0 : Vec d)) hε.le
    (by linarith : ε < 2 * ε)
  have hcont : Continuous (classicalGradient (pointRemovalCutoff (d := d) ε)) :=
    PDE.ContDiff.continuous_classicalGradient (hsmooth.of_le (by simp))
  exact hcont.memLp_of_hasCompactSupport
    (pointRemovalCutoff_gradient_hasCompactSupport hε)

/-- Radius-dependent bound from which the uniform point-removal estimate follows. -/
theorem pointRemovalCutoff_gradient_eLpNorm_two_le {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (classicalGradient (pointRemovalCutoff (d := d) ε)) 2 volume ≤
      ENNReal.ofReal (32 / ε) *
        volume (euclideanBall (0 : Vec d) (2 * ε)) ^ (1 / (2 : ℝ)) := by
  let f := classicalGradient (pointRemovalCutoff (d := d) ε)
  have hsupport : Function.support f ⊆ euclideanBall (0 : Vec d) (2 * ε) := by
    intro x hx
    by_contra hxb
    have hr : 2 * ε ≤ vecEuclideanNorm x := by
      rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < 2 * ε)] at hxb
      simpa using not_lt.mp hxb
    exact hx (pointRemovalCutoff_gradient_zero hε hr)
  have hzero : Function.support (0 : Vec d → Vec d) ⊆
      euclideanBall (0 : Vec d) (2 * ε) := by simp
  have hfm : AEStronglyMeasurable (f - (0 : Vec d → Vec d)) volume := by
    rw [sub_zero]
    exact (pointRemovalCutoff_gradient_memLp_two hε).aestronglyMeasurable
  have hb := eLpNorm_sub_le_of_dist_bdd (μ := volume) (p := (2 : ℝ≥0∞))
    (by norm_num) (measurableSet_euclideanBall (0 : Vec d) (2 * ε)).nullMeasurableSet
    (c := 32 / ε) (by positivity)
    (f := f) (g := (0 : Vec d → Vec d)) hfm
    (fun x => by
      rw [Pi.zero_apply, dist_zero_right]
      exact (norm_le_vecEuclideanNorm _).trans
        (pointRemovalCutoff_gradient_bound hε x))
    hsupport hzero
  simpa [f] using hb


theorem pointRemovalCutoff_gradient_eLpNorm_two_uniform {d : ℕ}
    (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    eLpNorm (classicalGradient (pointRemovalCutoff (d := d) ε)) 2 volume ≤
      ENNReal.ofReal 32 *
        (ENNReal.ofReal ((2 : ℝ) ^ d) *
          volume (euclideanBall (0 : Vec d) 1)) ^ (1 / (2 : ℝ)) := by
  refine (pointRemovalCutoff_gradient_eLpNorm_two_le hε).trans ?_
  rw [volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec d)
    (by positivity : 0 < 2 * ε)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hepow : ε ^ d ≤ ε ^ 2 := by
    exact pow_le_pow_of_le_one hε.le hε1 hd
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


theorem tendsto_pointRemovalCutoff_zero_of_ne_zero {d : ℕ}
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    {x : Vec d} (hx : x ≠ 0) :
    Tendsto (fun n => pointRemovalCutoff (ε n) x) atTop (𝓝 0) := by
  have hxnorm : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hx
  have hscaled : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hε0
  have hev : ∀ᶠ n in atTop, 2 * ε n < vecEuclideanNorm x :=
    (tendsto_order.1 hscaled).2 _ hxnorm
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hev] with n hn
  exact pointRemovalCutoff_zero (hε n) hn.le


end

end PDE
